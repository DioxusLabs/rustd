//! Monomorphization of mir, which is used in mir interpreter and const eval.
//!
//! The job of monomorphization is:
//! * Monomorphization. That is, replacing `Option<T>` with `Option<i32>` where `T:=i32` substitution
//!   is provided
//! * Normalizing types, for example replacing RPIT of other functions called in this body.
//!
//! So the monomorphization should be called even if the substitution is empty.

use rustc_next_trait_solver::placeholder::BoundVarReplacer;
use rustc_type_ir::inherent::{IntoKind, Ty as _};
use rustc_type_ir::{
    FallibleTypeFolder, Interner, TypeFlags, TypeFoldable, TypeSuperFoldable, TypeVisitableExt,
    UniverseIndex,
};

use crate::{
    InferBodyId, ParamEnvAndCrate,
    next_solver::{
        Allocation, AllocationData, Const, ConstKind, Region, RegionKind, StoredConst,
        StoredGenericArgs, StoredTy,
    },
    traits::StoredParamEnvAndCrate,
};
use crate::{
    db::{HirDatabase, InternedClosureId, InternedCoroutineId, InternedOpaqueTyId},
    next_solver::{
        AliasTy, AliasTyKind, Binder, DbInterner, GenericArgs, SolverDefId, Ty, TyKind, TypingMode,
        infer::{DbInternerInferExt, InferCtxt, traits::ObligationCause},
        obligation_ctxt::ObligationCtxt,
        references_non_lt_error,
        util::PlaceholderReplacer,
    },
};

use super::{MirBody, MirLowerError, Operand, OperandKind, Rvalue, StatementKind, TerminatorKind};

struct Filler<'db> {
    infcx: InferCtxt<'db>,
    trait_env: ParamEnvAndCrate<'db>,
    subst: GenericArgs<'db>,
    /// One entry for each binder the fold is inside of, as normalization wants them.
    universes: Vec<Option<UniverseIndex>>,
}

impl<'db> FallibleTypeFolder<DbInterner<'db>> for Filler<'db> {
    type Error = MirLowerError<'db>;

    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn try_fold_binder<T: TypeFoldable<DbInterner<'db>>>(
        &mut self,
        t: Binder<'db, T>,
    ) -> Result<Binder<'db, T>, Self::Error> {
        self.universes.push(None);
        let t = t.try_super_fold_with(self);
        self.universes.pop();
        t
    }

    fn try_fold_ty(&mut self, ty: Ty<'db>) -> Result<Ty<'db>, Self::Error> {
        if !ty.has_type_flags(TypeFlags::HAS_ALIAS | TypeFlags::HAS_PARAM) {
            return Ok(ty);
        }

        match ty.kind() {
            TyKind::Alias(..) => {
                // First instantiate params.
                let ty = ty.try_super_fold_with(self)?;
                let ty = self.impl_opaque(ty);

                // Reveal one opaque at a time so nested trait RPITs pass through impl_opaque
                // before the solver can normalize them as bodyless trait methods.
                if let TyKind::Alias(AliasTy {
                    kind: AliasTyKind::Opaque { def_id }, args, ..
                }) = ty.kind()
                {
                    let hidden = self
                        .infcx
                        .interner
                        .type_of(def_id.into())
                        .instantiate(self.infcx.interner, args)
                        .skip_norm_wip();
                    return hidden.try_fold_with(self);
                }

                let ty = self.normalized(ty)?;
                // Normalization could introduce infer vars (for example, if the alias cannot be normalized),
                // and we must not have infer vars in the body.
                let ty = ty.replace_infer_with_error(self.infcx.interner);
                ty.try_super_fold_with(self)
            }
            TyKind::Param(param) => {
                let ty = self
                    .subst
                    .as_slice()
                    .get(param.index as usize)
                    .and_then(|arg| arg.ty())
                    .ok_or_else(|| {
                    MirLowerError::GenericArgNotProvided(param.id.into(), self.subst.store())
                })?;
                // An argument can be the `impl Future` of an `async fn`, which the body of
                // the caller only knows by that name.
                if ty.has_type_flags(TypeFlags::HAS_TY_OPAQUE) {
                    return self.try_fold_ty(ty);
                }
                Ok(ty)
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_const(&mut self, ct: Const<'db>) -> Result<Const<'db>, Self::Error> {
        let ConstKind::Param(param) = ct.kind() else {
            return ct.try_super_fold_with(self);
        };
        self.subst.as_slice().get(param.index as usize).and_then(|arg| arg.konst()).ok_or_else(
            || MirLowerError::GenericArgNotProvided(param.id.into(), self.subst.store()),
        )
    }

    fn try_fold_region(&mut self, region: Region<'db>) -> Result<Region<'db>, Self::Error> {
        let RegionKind::ReEarlyParam(param) = region.kind() else {
            return Ok(region);
        };
        // A function generic over nothing but lifetimes is monomorphized without arguments,
        // and what its lifetimes are makes no difference to the code.
        let region = self.subst.as_slice().get(param.index as usize).and_then(|arg| arg.region());
        Ok(region.unwrap_or_else(|| Region::new_erased(self.infcx.interner)))
    }
}

impl<'db> Filler<'db> {
    /// `alias` as what it is an alias of. One that names the lifetimes of a binder around it,
    /// like `D::Data<'a>` in `for<'a> fn(&'a mut T) -> D::Data<'a>`, is normalized with
    /// placeholders in their place, which are put back afterwards.
    fn normalized(&mut self, alias: Ty<'db>) -> Result<Ty<'db>, MirLowerError<'db>> {
        let normalize = |ty| {
            ObligationCtxt::new(&self.infcx)
                .structurally_normalize_ty(&ObligationCause::dummy(), self.trait_env.param_env, ty)
                .map_err(|_| MirLowerError::NotSupported("can't normalize alias".to_owned()))
        };
        if !alias.has_escaping_bound_vars() {
            return normalize(alias);
        }
        let (alias, regions, types, consts) =
            BoundVarReplacer::replace_bound_vars(&self.infcx, &mut self.universes, alias);
        let ty = normalize(alias)?;
        Ok(PlaceholderReplacer::replace_placeholders(
            &self.infcx,
            regions,
            types,
            consts,
            &self.universes,
            ty,
        ))
    }

    fn new(db: &'db dyn HirDatabase, env: ParamEnvAndCrate<'db>, subst: GenericArgs<'db>) -> Self {
        let interner = DbInterner::new_with(db, env.krate);
        let infcx = interner.infer_ctxt().build(TypingMode::PostAnalysis);
        Self { infcx, trait_env: env, subst, universes: Vec::new() }
    }

    /// The `impl Trait` a trait method returns is the one of the impl's method once the
    /// implementing type is known.
    fn impl_opaque(&self, ty: Ty<'db>) -> Ty<'db> {
        let TyKind::Alias(alias) = ty.kind() else { return ty };
        let AliasTyKind::Opaque { def_id } = alias.kind else { return ty };
        let SolverDefId::InternedOpaqueTyId(opaque) = def_id.into() else { return ty };
        let db = self.infcx.interner.db;
        let crate::ImplTraitId::ReturnTypeImplTrait(func, idx) = opaque.loc(db) else {
            return ty;
        };
        // A lifetime nothing settled is an error one, and no code depends on it.
        if alias.args.has_type_flags(TypeFlags::HAS_PARAM) || references_non_lt_error(&alias.args) {
            return ty;
        }
        let (either::Either::Left(implemented), args) =
            db.lookup_impl_method(self.trait_env, func, alias.args)
        else {
            return ty;
        };
        if implemented == func {
            return ty;
        }
        let opaque =
            InternedOpaqueTyId::new(db, crate::ImplTraitId::ReturnTypeImplTrait(implemented, idx));
        Ty::new_alias(
            self.infcx.interner,
            AliasTy::new_from_args(
                self.infcx.interner,
                AliasTyKind::Opaque { def_id: opaque.into() },
                args,
            ),
        )
    }

    fn fill_ty(&mut self, t: &mut StoredTy) -> Result<(), MirLowerError<'db>> {
        // Can't deep normalized as that'll try to normalize consts and fail.
        *t = t.as_ref().try_fold_with(self)?.store();
        if references_non_lt_error(&t.as_ref()) {
            Err(MirLowerError::NotSupported(format!(
                "monomorphization resulted in errors: {:?}",
                t.as_ref()
            )))
        } else {
            Ok(())
        }
    }

    fn fill_const(&mut self, t: &mut StoredConst) -> Result<(), MirLowerError<'db>> {
        // Can't deep normalized as that'll try to normalize consts and fail.
        *t = t.as_ref().try_fold_with(self)?.store();
        if references_non_lt_error(&t.as_ref()) {
            Err(MirLowerError::NotSupported(format!(
                "monomorphization resulted in errors: {:?}",
                t.as_ref()
            )))
        } else {
            Ok(())
        }
    }

    fn fill_args(&mut self, t: &mut StoredGenericArgs) -> Result<(), MirLowerError<'db>> {
        // Can't deep normalized as that'll try to normalize consts and fail.
        *t = t.as_ref().try_fold_with(self)?.store();
        if references_non_lt_error(&t.as_ref()) {
            Err(MirLowerError::NotSupported(format!(
                "monomorphization resulted in errors: {:?}",
                t.as_ref()
            )))
        } else {
            Ok(())
        }
    }

    fn fill_operand(&mut self, op: &mut Operand) -> Result<(), MirLowerError<'db>> {
        match &mut op.kind {
            OperandKind::Constant { konst, ty } => {
                self.fill_const(konst)?;
                self.fill_ty(ty)?;
            }
            OperandKind::Allocation { allocation } => {
                let alloc = allocation.as_ref();
                let mut ty = alloc.ty.store();
                self.fill_ty(&mut ty)?;
                *allocation = Allocation::new(AllocationData {
                    ty: ty.as_ref(),
                    memory: alloc.memory.clone(),
                    // FIXME: Do we need to fill the memory map too?
                    memory_map: alloc.memory_map.clone(),
                })
                .store();
            }
            OperandKind::Copy(_) | OperandKind::Move(_) | OperandKind::Static(_) => (),
        }
        Ok(())
    }

    fn fill_body(&mut self, body: &mut MirBody<'db>) -> Result<(), MirLowerError<'db>> {
        for (_, l) in body.locals.iter_mut() {
            self.fill_ty(&mut l.ty)?;
        }
        for (_, bb) in body.basic_blocks.iter_mut() {
            for statement in &mut bb.statements {
                match &mut statement.kind {
                    StatementKind::Assign(_, r) => match r {
                        Rvalue::Aggregate(ak, ops) => {
                            for op in &mut **ops {
                                self.fill_operand(op)?;
                            }
                            match ak {
                                super::AggregateKind::Array(ty)
                                | super::AggregateKind::Tuple(ty)
                                | super::AggregateKind::Closure(ty) => self.fill_ty(ty)?,
                                super::AggregateKind::Adt(_, subst) => self.fill_args(subst)?,
                                super::AggregateKind::Union(_, _) => (),
                            }
                        }
                        Rvalue::Use(op) => {
                            self.fill_operand(op)?;
                        }
                        Rvalue::Repeat(op, len) => {
                            self.fill_operand(op)?;
                            self.fill_const(len)?;
                        }
                        Rvalue::Cast(_, op, ty) => {
                            self.fill_operand(op)?;
                            self.fill_ty(ty)?;
                        }
                        Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                            self.fill_operand(lhs)?;
                            self.fill_operand(rhs)?;
                        }
                        Rvalue::UnaryOp(_, op) => {
                            self.fill_operand(op)?;
                        }
                        Rvalue::Ref(_, _)
                        | Rvalue::Len(_)
                        | Rvalue::Discriminant(_)
                        | Rvalue::CopyForDeref(_) => (),
                        Rvalue::ThreadLocalRef(n)
                        | Rvalue::AddressOf(n)
                        | Rvalue::BinaryOp(n)
                        | Rvalue::NullaryOp(n) => match *n {},
                    },
                    StatementKind::InlineAsm(asm) => {
                        for operand in &mut asm.operands {
                            match operand {
                                super::AsmOperand::Reg { input: Some(value), .. }
                                | super::AsmOperand::Const(value)
                                | super::AsmOperand::Sym(value) => self.fill_operand(value)?,
                                super::AsmOperand::Reg { input: None, .. }
                                | super::AsmOperand::Label => (),
                            }
                        }
                    }
                    StatementKind::Deinit(_)
                    | StatementKind::FakeRead(_)
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => (),
                }
            }
            if let Some(terminator) = &mut bb.terminator {
                match &mut terminator.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        self.fill_operand(func)?;
                        for op in &mut **args {
                            self.fill_operand(op)?;
                        }
                    }
                    TerminatorKind::SwitchInt { discr, .. } => {
                        self.fill_operand(discr)?;
                    }
                    TerminatorKind::Goto { .. }
                    | TerminatorKind::UnwindResume
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable
                    | TerminatorKind::Drop { .. }
                    | TerminatorKind::DropAndReplace { .. }
                    | TerminatorKind::Assert { .. }
                    | TerminatorKind::Yield { .. }
                    | TerminatorKind::CoroutineDrop
                    | TerminatorKind::FalseEdge { .. }
                    | TerminatorKind::FalseUnwind { .. } => (),
                }
            }
        }
        Ok(())
    }
}

/// `body` with `subst` in place of its generic parameters. The queries below keep the result;
/// a caller that needs it once asks here instead.
pub(crate) fn monomorphized<'db>(
    db: &'db dyn HirDatabase,
    body: &MirBody<'db>,
    subst: &StoredGenericArgs,
    trait_env: &StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    let mut filler = Filler::new(db, trait_env.as_ref(db), subst.as_ref());
    let mut body = body.clone();
    filler.fill_body(&mut body)?;
    Ok(body)
}

#[salsa::tracked(returns(as_ref), cycle_result = monomorphized_mir_body_cycle_result)]
pub fn monomorphized_mir_body_query<'db>(
    db: &'db dyn HirDatabase,
    owner: InferBodyId<'db>,
    subst: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    monomorphized(db, db.mir_body(owner)?, &subst, &trait_env)
}

/// The constant behind a promoted `&expr` of `owner`, as the instance with `subst` sees it.
#[salsa::tracked(returns(as_ref))]
pub fn monomorphized_promoted_mir_body_query<'db>(
    db: &'db dyn HirDatabase,
    owner: InferBodyId<'db>,
    expr: hir_def::hir::ExprId,
    subst: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    let body = super::promoted_mir_body_query(db, owner, expr).map_err(Clone::clone)?;
    monomorphized(db, body, &subst, &trait_env)
}

fn monomorphized_mir_body_cycle_result<'db>(
    _db: &'db dyn HirDatabase,
    _: salsa::Id,
    _: InferBodyId<'db>,
    _: StoredGenericArgs,
    _: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    Err(MirLowerError::Loop)
}

#[salsa::tracked(returns(as_ref), cycle_result = monomorphized_mir_body_for_closure_cycle_result)]
pub fn monomorphized_mir_body_for_closure_query<'db>(
    db: &'db dyn HirDatabase,
    closure: InternedClosureId<'db>,
    subst: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    monomorphized(db, db.mir_body_for_closure(closure)?, &subst, &trait_env)
}

fn monomorphized_mir_body_for_closure_cycle_result<'db>(
    _db: &'db dyn HirDatabase,
    _: salsa::Id,
    _: InternedClosureId<'db>,
    _: StoredGenericArgs,
    _: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    Err(MirLowerError::Loop)
}

#[salsa::tracked(returns(as_ref), cycle_result = monomorphized_mir_body_for_coroutine_cycle_result)]
pub fn monomorphized_mir_body_for_coroutine_query<'db>(
    db: &'db dyn HirDatabase,
    coroutine: InternedCoroutineId<'db>,
    subst: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    monomorphized(db, db.mir_body_for_coroutine(coroutine)?, &subst, &trait_env)
}

#[salsa::tracked(returns(as_ref), cycle_result = monomorphized_mir_body_for_coroutine_cycle_result)]
pub fn monomorphized_mir_body_for_coroutine_by_move_query<'db>(
    db: &'db dyn HirDatabase,
    coroutine: InternedCoroutineId<'db>,
    subst: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    monomorphized(db, db.mir_body_for_coroutine_by_move(coroutine)?, &subst, &trait_env)
}

fn monomorphized_mir_body_for_coroutine_cycle_result<'db>(
    _db: &'db dyn HirDatabase,
    _: salsa::Id,
    _: InternedCoroutineId<'db>,
    _: StoredGenericArgs,
    _: StoredParamEnvAndCrate,
) -> Result<MirBody<'db>, MirLowerError<'db>> {
    Err(MirLowerError::Loop)
}
