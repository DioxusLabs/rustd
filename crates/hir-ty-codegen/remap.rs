use hir_def::{AdtId, AttrDefId, FunctionId, HasModule, VariantId};

use super::CodegenError;
use super::{
    AggregateKind, MirBody, Operand, OperandKind, ProjectionElem, Result, Rvalue, Sharing,
    StatementKind, TerminatorKind,
};
use crate::layout::{Layout, LayoutError, LayoutProvider};
use crate::next_solver::{StoredGenericArgs, StoredTy};
use crate::traits::StoredParamEnvAndCrate;
use crate::{
    db::HirDatabase,
    next_solver::{Allocation, AllocationData},
};
use triomphe::Arc;

pub(super) fn monomorphized<'db>(
    db: &'db dyn HirDatabase,
    sharing: &Sharing,
    body: &MirBody<'db>,
    args: &StoredGenericArgs,
    env: &StoredParamEnvAndCrate,
) -> std::result::Result<MirBody<'db>, super::super::MirLowerError<'db>> {
    use rustc_type_ir::Interner;
    let interner = crate::next_solver::DbInterner::new_with(db, env.krate);
    crate::mir::monomorphization::monomorphized_with(db, body, args, env, &|id, args| {
        if let crate::ImplTraitId::ReturnTypeImplTrait(func, index) = id.loc(db)
            && let Some(source) = sharing.body_source(db, func)
        {
            let source_id = crate::db::InternedOpaqueTyId::new(
                db,
                crate::ImplTraitId::ReturnTypeImplTrait(source, index),
            );
            let hidden = interner.type_of(source_id.into()).instantiate_identity().skip_norm_wip();
            let hidden = sharing.analysis_fold(db, source, hidden);
            return crate::next_solver::EarlyBinder::bind(hidden)
                .instantiate(interner, args)
                .skip_norm_wip();
        }
        interner.type_of(id.into()).instantiate(interner, args).skip_norm_wip()
    })
}

struct ProgramLayout<'a, 'db> {
    db: &'db dyn HirDatabase,
    sharing: &'a Sharing,
}

impl<'db> LayoutProvider<'db> for ProgramLayout<'_, 'db> {
    fn coroutine_is_by_move(
        &self,
        id: crate::db::InternedCoroutineId<'db>,
        args: rustc_type_ir::CoroutineArgs<crate::next_solver::DbInterner<'db>>,
    ) -> bool {
        self.sharing.coroutine_is_by_move(self.db, id, args)
    }
    fn db(&self) -> &'db dyn HirDatabase {
        self.db
    }
    fn layout(
        &self,
        ty: StoredTy,
        env: StoredParamEnvAndCrate,
    ) -> std::result::Result<Arc<Layout>, LayoutError> {
        layout(self.db, ty, env, self.sharing.clone())
    }
    fn adt(
        &self,
        def: AdtId,
        args: StoredGenericArgs,
        env: StoredParamEnvAndCrate,
    ) -> std::result::Result<Arc<Layout>, LayoutError> {
        crate::layout::adt::layout_of_adt_with(self.db, def, args, env, self)
    }
    fn coroutine(
        &self,
        id: crate::db::InternedCoroutineId<'db>,
        args: StoredGenericArgs,
        env: StoredParamEnvAndCrate,
        by_move: bool,
    ) -> std::result::Result<std::borrow::Cow<'db, MirBody<'db>>, LayoutError> {
        use salsa::plumbing::AsId;
        let def = if by_move {
            super::InstanceDef::CoroutineByMove(id.as_id())
        } else {
            super::InstanceDef::Coroutine(id.as_id())
        };
        super::program_instance_body(
            self.db,
            &super::Instance { def, args, checked: false },
            env,
            self.sharing,
        )
        .map_err(|e| {
            if std::env::var_os("RUSTD_CFG_SHARING_TRACE").is_some() {
                eprintln!("sharing coroutine layout error: {id:?}: {e:?}");
            }
            LayoutError::Unknown
        })
    }
}

#[salsa::tracked(returns(clone), cycle_result = layout_cycle)]
pub(super) fn layout(
    db: &dyn HirDatabase,
    ty: StoredTy,
    env: StoredParamEnvAndCrate,
    sharing: Sharing,
) -> std::result::Result<Arc<Layout>, LayoutError> {
    if sharing.is_empty() {
        return db.layout_of_ty(ty, env);
    }
    crate::layout::layout_of_ty_with(db, ty, env, &ProgramLayout { db, sharing: &sharing })
}

fn layout_cycle(
    _: &dyn HirDatabase,
    _: salsa::Id,
    _: StoredTy,
    _: StoredParamEnvAndCrate,
    _: Sharing,
) -> std::result::Result<Arc<Layout>, LayoutError> {
    Err(LayoutError::RecursiveTypeWithoutIndirection)
}

pub(super) fn body<'db>(
    db: &'db dyn HirDatabase,
    sharing: &Sharing,
    source: FunctionId,
    original: &MirBody<'db>,
) -> Result<MirBody<'db>> {
    mapped_body(db, sharing, Some(source), original)
}

pub(super) fn opaques<'db>(
    db: &'db dyn HirDatabase,
    sharing: &Sharing,
    original: &MirBody<'db>,
) -> Result<MirBody<'db>> {
    mapped_body(db, sharing, None, original)
}

#[salsa::tracked(returns(ref))]
pub(super) fn promoted<'db>(
    db: &'db dyn HirDatabase,
    source: FunctionId,
    expr: hir_def::hir::ExprId,
    args: StoredGenericArgs,
    env: StoredParamEnvAndCrate,
    sharing: Sharing,
) -> Result<MirBody<'db>> {
    let raw = super::super::promoted_mir_body_query(db, source.into(), expr)
        .map_err(|e| CodegenError::Frontend(format!("promoted mir: {e:?}")))?;
    let mapped = body(db, &sharing, source, &raw)?;
    monomorphized(db, &sharing, &mapped, &args, &env)
        .map_err(|e| CodegenError::Frontend(format!("promoted mir: {e:?}")))
}

fn mapped_body<'db>(
    db: &'db dyn HirDatabase,
    sharing: &Sharing,
    source: Option<FunctionId>,
    original: &MirBody<'db>,
) -> Result<MirBody<'db>> {
    let mut body = original.clone();
    let item = |item| source.map_or(item, |source| sharing.analysis_item(db, source, item));
    let krate = original.owner.module(db).krate(db);
    let variant = |variant| match variant {
        VariantId::EnumVariantId(id) => match item(AttrDefId::EnumVariantId(id)) {
            AttrDefId::EnumVariantId(id) => VariantId::EnumVariantId(id),
            _ => variant,
        },
        VariantId::StructId(id) => match item(AdtId::StructId(id).into()) {
            AttrDefId::AdtId(AdtId::StructId(id)) => VariantId::StructId(id),
            _ => variant,
        },
        VariantId::UnionId(id) => match item(AdtId::UnionId(id).into()) {
            AttrDefId::AdtId(AdtId::UnionId(id)) => VariantId::UnionId(id),
            _ => variant,
        },
    };
    macro_rules! fold {
        ($value:expr) => {
            *$value = match source {
                Some(source) => sharing.analysis_fold(db, source, $value.as_ref()),
                None => sharing.reuse_opaques(db, krate, $value.as_ref()),
            }
            .store()
        };
    }
    let operand = |op: &mut Operand| -> Result<()> {
        match &mut op.kind {
            OperandKind::Constant { konst, ty } => {
                fold!(konst);
                fold!(ty);
            }
            OperandKind::Allocation { allocation } => {
                let value = allocation.as_ref();
                if source.is_some() && matches!(value.memory_map, crate::MemoryMap::Complex(_)) {
                    return Err(CodegenError::Unsupported(
                        "analysis-sharing a complex allocation".into(),
                    ));
                }
                *allocation = Allocation::new(AllocationData {
                    ty: match source {
                        Some(source) => sharing.analysis_fold(db, source, value.ty),
                        None => sharing.reuse_opaques(db, krate, value.ty),
                    },
                    memory: value.memory.clone(),
                    memory_map: value.memory_map.clone(),
                })
                .store();
            }
            OperandKind::Static(id) => {
                if let AttrDefId::StaticId(mapped) = item((*id).into()) {
                    *id = mapped;
                }
            }
            OperandKind::Copy(_) | OperandKind::Move(_) => {}
        }
        Ok(())
    };
    for (_, local) in body.locals.iter_mut() {
        fold!(&mut local.ty);
    }
    body.walk_places(|place| {
        place.projection = super::super::Projection::new_from_iter(
            place.projection.as_slice().iter().map(|&elem| match elem {
                ProjectionElem::Downcast(id) => ProjectionElem::Downcast(variant(id)),
                elem => elem,
            }),
        )
        .store();
    });
    for (_, block) in body.basic_blocks.iter_mut() {
        for statement in &mut block.statements {
            match &mut statement.kind {
                StatementKind::Assign(_, value) => match value {
                    Rvalue::Aggregate(kind, operands) => {
                        for op in &mut **operands {
                            operand(op)?;
                        }
                        match kind {
                            AggregateKind::Array(ty)
                            | AggregateKind::Tuple(ty)
                            | AggregateKind::Closure(ty) => {
                                fold!(ty);
                            }
                            AggregateKind::Adt(id, args) => {
                                *id = variant(*id);
                                fold!(args);
                            }
                            AggregateKind::Union(id, field) => {
                                if let VariantId::UnionId(mapped) = variant(VariantId::UnionId(*id))
                                {
                                    *id = mapped;
                                    field.parent = VariantId::UnionId(mapped);
                                }
                            }
                        }
                    }
                    Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => operand(op)?,
                    Rvalue::Repeat(op, len) => {
                        operand(op)?;
                        fold!(len);
                    }
                    Rvalue::Cast(_, op, ty) => {
                        operand(op)?;
                        fold!(ty);
                    }
                    Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                        operand(lhs)?;
                        operand(rhs)?;
                    }
                    Rvalue::Ref(..)
                    | Rvalue::Len(_)
                    | Rvalue::Discriminant(_)
                    | Rvalue::CopyForDeref(_) => {}
                    Rvalue::ThreadLocalRef(n)
                    | Rvalue::AddressOf(n)
                    | Rvalue::BinaryOp(n)
                    | Rvalue::NullaryOp(n) => match *n {},
                },
                StatementKind::InlineAsm(asm) => {
                    for op in &mut asm.operands {
                        match op {
                            super::super::AsmOperand::Reg { input: Some(op), .. }
                            | super::super::AsmOperand::Const(op)
                            | super::super::AsmOperand::Sym(op) => operand(op)?,
                            super::super::AsmOperand::Reg { input: None, .. }
                            | super::super::AsmOperand::Label => {}
                        }
                    }
                }
                StatementKind::Deinit(_)
                | StatementKind::FakeRead(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
            }
        }
        if let Some(terminator) = &mut block.terminator {
            match &mut terminator.kind {
                TerminatorKind::Call { func, args, .. } => {
                    operand(func)?;
                    for op in &mut **args {
                        operand(op)?;
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => operand(discr)?,
                TerminatorKind::DropAndReplace { value, .. }
                | TerminatorKind::Yield { value, .. } => operand(value)?,
                TerminatorKind::Assert { cond, .. } => operand(cond)?,
                TerminatorKind::Goto { .. }
                | TerminatorKind::UnwindResume
                | TerminatorKind::Abort
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::Drop { .. }
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. } => {}
            }
        }
    }
    Ok(body)
}
