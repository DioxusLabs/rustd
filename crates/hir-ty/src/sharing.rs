//! Diagnostic eligibility, without changing semantic or compilation identities.
//!
//! The reference inventory follows rustc's `MirNeighborCollector` in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_monomorphize/src/collector.rs>:
//! function operands, constants, statics, drops and unsizing can introduce code dependencies.
//! Concrete calls use the selected impl; unresolved dispatch and vtables retain
//! local impls whose instantiated trait arguments can unify. PairSafety must hold
//! before using either diagnostic sharing class.
//! Textual macro escape follows `define_macro` and module visitation in
//! `rustc_resolve/src/build_reduced_graph.rs` at the same rustc tag.

use std::collections::VecDeque;

use base_db::Crate;
use hir_def::{
    AdtId, AttrDefId, CallableDefId, DefWithBodyId, FunctionId, GenericDefId, HasModule, ImplId,
    ItemContainerId, Lookup, ModuleDefId, TraitId, VariantId,
    attrs::AttrFlags,
    expr_store::Body,
    hir::{Expr, Pat, generics::GenericParams},
    resolver::{HasResolver, ValueNs},
    signatures::{ConstSignature, FunctionSignature, ImplSignature, TypeAliasSignature},
    twins::{crate_items, scope_pairs, twin_index},
};
use hir_expand::mod_path::{ModPath, PathKind};
use petgraph::{algo::kosaraju_scc, graph::DiGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{
    TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable,
    TypeVisitableExt, TypeVisitor, inherent::IntoKind,
};

use crate::{
    InferenceResult, Span, TyDefId,
    db::{GeneralConstId, HirDatabase},
    lower::GenericPredicates,
    method_resolution::CandidateId,
    mir::{Operand, OperandKind, Rvalue, StatementKind, TerminatorKind},
    next_solver::{
        AliasTyKind, ClauseKind, Const, ConstKind, DbInterner, ExistentialPredicate, GenericArgs,
        TraitRef, Ty, TyKind, TypingMode,
        infer::{DbInternerInferExt, InferCtxt, traits::ObligationCause},
    },
    traits::ParamEnvAndCrate,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rejection {
    CfgDiffering,
    Transitive,
    GenericUnresolved,
    Unknown,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Eligibility {
    /// Fully shareable T items before the crate-wide safety veto.
    pub candidates: FxHashSet<AttrDefId>,
    pub analysis_shared: FxHashSet<AttrDefId>,
    pub rejected: FxHashMap<AttrDefId, Rejection>,
    pub pair_veto: Vec<&'static str>,
    pub statics: usize,
    pub test_only_statics: usize,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct References {
    items: FxHashSet<AttrDefId>,
    unknown: bool,
    generic_unresolved: bool,
}

struct Collector<'db> {
    db: &'db dyn HirDatabase,
    krate: Crate,
    env: ParamEnvAndCrate<'db>,
    result: References,
    seen: FxHashSet<Ty<'db>>,
    traits: FxHashSet<TraitRef<'db>>,
    coroutines: FxHashSet<crate::db::InternedCoroutineId<'db>>,
}

struct CandidateArgs<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
    types: FxHashMap<Ty<'db>, Ty<'db>>,
    consts: FxHashMap<Const<'db>, Const<'db>>,
}

impl<'db> TypeFolder<DbInterner<'db>> for CandidateArgs<'_, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.infcx.interner
    }

    fn fold_ty(&mut self, ty: Ty<'db>) -> Ty<'db> {
        if matches!(
            ty.kind(),
            TyKind::Param(_)
                | TyKind::Alias(_)
                | TyKind::Dynamic(..)
                | TyKind::Error(_)
                | TyKind::Bound(..)
                | TyKind::Placeholder(_)
        ) {
            *self.types.entry(ty).or_insert_with(|| self.infcx.next_ty_var(Span::Dummy))
        } else {
            ty.super_fold_with(self)
        }
    }

    fn fold_const(&mut self, value: Const<'db>) -> Const<'db> {
        if matches!(
            value.kind(),
            ConstKind::Param(_) | ConstKind::Unevaluated(_) | ConstKind::Error(_)
        ) {
            *self.consts.entry(value).or_insert_with(|| self.infcx.next_const_var(Span::Dummy))
        } else {
            value.super_fold_with(self)
        }
    }
}

fn generic(item: AttrDefId) -> Option<GenericDefId> {
    Some(match item {
        AttrDefId::FunctionId(id) => id.into(),
        AttrDefId::ConstId(id) => id.into(),
        AttrDefId::StaticId(id) => id.into(),
        AttrDefId::AdtId(id) => id.into(),
        AttrDefId::ImplId(id) => id.into(),
        AttrDefId::TraitId(id) => id.into(),
        AttrDefId::TypeAliasId(id) => id.into(),
        _ => return None,
    })
}

fn body(db: &dyn HirDatabase, item: AttrDefId) -> Option<DefWithBodyId> {
    match item {
        AttrDefId::FunctionId(id) if FunctionSignature::of(db, id).has_body() => Some(id.into()),
        AttrDefId::ConstId(id) if ConstSignature::of(db, id).has_body() => Some(id.into()),
        AttrDefId::StaticId(id) => Some(id.into()),
        AttrDefId::EnumVariantId(id) => {
            let body = Body::of(db, id.into());
            (!matches!(body[body.root_expr()], Expr::Missing)).then_some(id.into())
        }
        _ => None,
    }
}

#[salsa::tracked(returns(ref))]
fn local_trait_impls(db: &dyn HirDatabase, krate: Crate) -> FxHashMap<TraitId, Vec<ImplId>> {
    let mut result: FxHashMap<TraitId, Vec<ImplId>> = FxHashMap::default();
    for &item in &crate_items(db, krate).items {
        if let AttrDefId::ImplId(id) = item
            && let Some(tr) = db.impl_trait(id)
        {
            result.entry(tr.skip_binder().def_id.0).or_default().push(id);
        }
    }
    result
}

impl<'db> Collector<'db> {
    fn trait_impls(&mut self, trait_ref: TraitRef<'db>) {
        if !self.traits.insert(trait_ref) {
            return;
        }
        let id = trait_ref.def_id.0;
        self.result.items.insert(id.into());
        let infcx =
            DbInterner::new_with(self.db, self.krate).infer_ctxt().build(TypingMode::PostAnalysis);
        let trait_ref = rustc_type_ir::fold_regions(infcx.interner, trait_ref, |_, _| {
            crate::next_solver::Region::new_erased(infcx.interner)
        });
        let trait_ref = if trait_ref.has_escaping_bound_vars() {
            trait_ref
        } else {
            infcx
                .at(&ObligationCause::dummy(), self.env.param_env)
                .deeply_normalize(trait_ref)
                .unwrap_or(trait_ref)
        };
        if !trait_ref.has_escaping_bound_vars()
            && let Some((selected, _)) =
                crate::method_resolution::find_matching_impl(&infcx, self.env.param_env, trait_ref)
        {
            if let crate::next_solver::AnyImplId::ImplId(id) = selected {
                self.result.items.insert(id.into());
            }
            return;
        }
        if let Some(impls) = local_trait_impls(self.db, self.krate).get(&id) {
            for &id in impls {
                let (applicable, unresolved) = infcx.probe(|_| {
                    let args = infcx.fresh_args_for_item(Span::Dummy, id.into());
                    let candidate = self
                        .db
                        .impl_trait(id)
                        .unwrap()
                        .instantiate(infcx.interner, args)
                        .skip_norm_wip();
                    if trait_ref.has_escaping_bound_vars() || candidate.has_escaping_bound_vars() {
                        return (true, true);
                    }
                    let mut folder = CandidateArgs {
                        infcx: &infcx,
                        types: FxHashMap::default(),
                        consts: FxHashMap::default(),
                    };
                    let target = trait_ref.fold_with(&mut folder);
                    let unresolved = !folder.types.is_empty()
                        || !folder.consts.is_empty()
                        || target.has_non_region_infer();
                    let candidate = candidate.fold_with(&mut folder);
                    let applicable = infcx
                        .at(&ObligationCause::dummy(), self.env.param_env)
                        .eq(target, candidate)
                        .is_ok();
                    (applicable, unresolved)
                });
                if applicable && unresolved {
                    self.result.items.insert(id.into());
                } else if applicable {
                    self.result.generic_unresolved = true;
                }
            }
        }
    }

    fn bounds(&mut self, def: GenericDefId, args: GenericArgs<'db>) {
        let interner = DbInterner::new_with(self.db, self.krate);
        for clause in
            GenericPredicates::query_all(self.db, def).iter_instantiated(interner, args.as_slice())
        {
            let clause = clause.skip_norm_wip();
            if let ClauseKind::Trait(pred) = clause.kind().skip_binder() {
                self.trait_impls(pred.trait_ref);
            }
            clause.visit_with(self);
        }
    }

    fn function(&mut self, func: FunctionId, args: GenericArgs<'db>) {
        args.visit_with(self);
        let interner = DbInterner::new_with(self.db, self.krate);
        let args = rustc_type_ir::fold_regions(interner, args, |_, _| {
            crate::next_solver::Region::new_erased(interner)
        });
        let (resolved, _) = if args.has_escaping_bound_vars() {
            (either::Either::Left(func), args)
        } else {
            self.db.lookup_impl_method(self.env, func, args)
        };
        self.bounds(func.into(), args);
        let either::Either::Left(resolved) = resolved else {
            if let ItemContainerId::TraitId(id) = func.lookup(self.db).container {
                let interner = DbInterner::new_with(self.db, self.krate);
                let count = GenericParams::of(self.db, id.into()).len();
                self.trait_impls(TraitRef::new_from_args(
                    interner,
                    id.into(),
                    GenericArgs::new_from_slice(&args[..count]),
                ));
            } else {
                self.result.generic_unresolved = true;
            }
            return;
        };
        self.result.items.insert(resolved.into());
        match resolved.lookup(self.db).container {
            ItemContainerId::ImplId(id) => {
                self.result.items.insert(id.into());
            }
            ItemContainerId::TraitId(id) => {
                let interner = DbInterner::new_with(self.db, self.krate);
                let count = GenericParams::of(self.db, id.into()).len();
                self.trait_impls(TraitRef::new_from_args(
                    interner,
                    id.into(),
                    GenericArgs::new_from_slice(&args[..count]),
                ));
            }
            _ => (),
        }
    }

    fn operand(&mut self, operand: &Operand) {
        match &operand.kind {
            OperandKind::Static(id) => {
                self.result.items.insert((*id).into());
            }
            OperandKind::Constant { konst, ty } => {
                ty.as_ref().visit_with(self);
                konst.as_ref().visit_with(self);
            }
            OperandKind::Allocation { allocation } => {
                let allocation = allocation.as_ref();
                allocation.ty.visit_with(self);
                if let crate::MemoryMap::Complex(map) = &allocation.memory_map {
                    self.result.items.extend(map.statics.iter().map(|s| AttrDefId::from(s.id)));
                    self.result.unknown = true;
                }
            }
            OperandKind::Copy(_) | OperandKind::Move(_) => (),
        }
    }
}

impl<'db> TypeVisitor<DbInterner<'db>> for Collector<'db> {
    type Result = ();

    fn visit_ty(&mut self, ty: Ty<'db>) {
        if !self.seen.insert(ty) {
            return;
        }
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                self.result.items.insert(adt.def_id().into());
                self.bounds(adt.def_id().into(), args);
            }
            TyKind::FnDef(def, args) => match def.0 {
                CallableDefId::FunctionId(id) => self.function(id, args),
                CallableDefId::StructId(id) => {
                    self.result.items.insert(AdtId::from(id).into());
                }
                CallableDefId::EnumVariantId(id) => {
                    self.result.items.insert(id.into());
                }
            },
            TyKind::Alias(alias) => match alias.kind {
                AliasTyKind::Projection { def_id } => match def_id.0.lookup(self.db).container {
                    ItemContainerId::TraitId(_) => {
                        self.trait_impls(
                            alias.trait_ref(DbInterner::new_with(self.db, self.krate)),
                        );
                    }
                    ItemContainerId::ImplId(id) => {
                        self.result.items.insert(id.into());
                    }
                    _ => self.result.generic_unresolved = true,
                },
                AliasTyKind::Opaque { .. } => {
                    if let Some(bounds) = ty.impl_trait_bounds(self.db) {
                        for clause in bounds {
                            if let ClauseKind::Trait(pred) = clause.kind().skip_binder() {
                                self.trait_impls(pred.trait_ref);
                            }
                            clause.visit_with(self);
                        }
                    } else {
                        self.result.generic_unresolved = true;
                    }
                }
                _ => self.result.generic_unresolved = true,
            },
            TyKind::Dynamic(bounds, _) => {
                for bound in bounds.iter() {
                    let interner = DbInterner::new_with(self.db, self.krate);
                    match bound.skip_binder() {
                        ExistentialPredicate::Trait(tr) => {
                            self.trait_impls(tr.with_self_ty(interner, ty))
                        }
                        ExistentialPredicate::AutoTrait(id) => {
                            self.trait_impls(TraitRef::new(interner, id, [ty]))
                        }
                        ExistentialPredicate::Projection(_) => (),
                    }
                }
            }
            TyKind::Coroutine(id, _) => {
                self.coroutines.insert(id.0);
            }
            TyKind::Closure(..) | TyKind::CoroutineClosure(..) | TyKind::CoroutineWitness(..) => (),
            TyKind::Error(..) | TyKind::Infer(..) => self.result.unknown = true,
            _ => (),
        }
        ty.super_visit_with(self);
    }

    fn visit_const(&mut self, konst: Const<'db>) {
        match konst.kind() {
            ConstKind::Unevaluated(uv) => match uv.def.0 {
                GeneralConstId::ConstId(id) => {
                    self.result.items.insert(id.into());
                }
                GeneralConstId::StaticId(id) => {
                    self.result.items.insert(id.into());
                }
                GeneralConstId::AnonConstId(_) => self.result.unknown = true,
            },
            ConstKind::Error(_) | ConstKind::Infer(_) => self.result.unknown = true,
            _ => (),
        }
        konst.super_visit_with(self);
    }
}

#[salsa::tracked(returns(ref))]
fn references(db: &dyn HirDatabase, item: AttrDefId, initializer: bool) -> References {
    let krate = item.module(db).krate(db);
    let env = ParamEnvAndCrate {
        param_env: generic(item)
            .map_or_else(crate::next_solver::ParamEnv::empty, |id| db.trait_environment(id)),
        krate,
    };
    let mut c = Collector {
        db,
        krate,
        env,
        result: References::default(),
        seen: FxHashSet::default(),
        traits: FxHashSet::default(),
        coroutines: FxHashSet::default(),
    };
    env.param_env.visit_with(&mut c);
    if let Some(def) = generic(item) {
        let interner = DbInterner::new_with(db, krate);
        use rustc_type_ir::inherent::GenericArgs as _;
        c.bounds(def, GenericArgs::identity_for_item(interner, def.into()));
        let defaults = db.generic_defaults(def);
        for index in 0..crate::generics::generics(db, def).len(false) {
            if let Some(default) = defaults.get(index) {
                default.skip_binder().visit_with(&mut c);
            }
        }
    }
    for clause in env.param_env.clauses().iter() {
        if let ClauseKind::Trait(pred) = clause.kind().skip_binder() {
            c.result.items.insert(pred.trait_ref.def_id.0.into());
        }
    }
    match item {
        AttrDefId::FunctionId(id) => {
            db.callable_item_signature(id.into()).skip_binder().visit_with(&mut c);
            match id.lookup(db).container {
                ItemContainerId::ImplId(id) => {
                    c.result.items.insert(id.into());
                }
                ItemContainerId::TraitId(id) => {
                    c.result.items.insert(id.into());
                }
                ItemContainerId::ExternBlockId(_) => c.result.unknown = true,
                _ => (),
            }
        }
        AttrDefId::ConstId(id) => {
            db.type_for_const(id).skip_binder().visit_with(&mut c);
        }
        AttrDefId::StaticId(id) => {
            db.type_for_static(id).skip_binder().visit_with(&mut c);
        }
        AttrDefId::TypeAliasId(id) => {
            if let ItemContainerId::TraitId(trait_id) = id.lookup(db).container
                && TypeAliasSignature::of(db, id).ty.is_none()
            {
                let interner = DbInterner::new_with(db, krate);
                use rustc_type_ir::inherent::GenericArgs as _;
                c.trait_impls(TraitRef::new_from_args(
                    interner,
                    trait_id.into(),
                    GenericArgs::identity_for_item(interner, trait_id.into()),
                ));
            } else {
                db.ty(TyDefId::TypeAliasId(id)).skip_binder().visit_with(&mut c);
            }
        }
        AttrDefId::ImplId(id) => {
            c.result
                .items
                .extend(id.impl_items(db).items.iter().map(|(_, item)| AttrDefId::from(*item)));
            db.impl_self_ty(id).skip_binder().visit_with(&mut c);
            if let Some(tr) = db.impl_trait(id) {
                c.result.items.insert(tr.skip_binder().def_id.0.into());
                tr.skip_binder().visit_with(&mut c);
            } else if ImplSignature::of(db, id).target_trait.is_some() {
                c.result.generic_unresolved = true;
            }
        }
        AttrDefId::AdtId(id) => {
            let variants: Vec<VariantId> = match id {
                AdtId::StructId(id) => vec![id.into()],
                AdtId::UnionId(id) => vec![id.into()],
                AdtId::EnumId(id) => id
                    .enum_variants(db)
                    .variants
                    .values()
                    .map(|(id, _)| {
                        c.result.items.insert((*id).into());
                        (*id).into()
                    })
                    .collect(),
            };
            for variant in variants {
                for (_, field) in db.field_types(variant).iter() {
                    field.ty().skip_binder().visit_with(&mut c);
                    if let Some(default) = field.default() {
                        default.skip_binder().visit_with(&mut c);
                    }
                }
            }
            // A definition-level graph must include destructors even for ADTs occurring only
            // under a pointer or in a signature; determining whether they drop is instance work.
            let drop_trait = hir_def::lang_item::lang_items(db, krate).Drop;
            for &item in &crate_items(db, krate).items {
                let AttrDefId::ImplId(impl_id) = item else { continue };
                if drop_trait.is_some()
                    && db
                        .impl_trait(impl_id)
                        .is_some_and(|tr| Some(tr.skip_binder().def_id.0) == drop_trait)
                    && matches!(db.impl_self_ty(impl_id).skip_binder().kind(), TyKind::Adt(adt, _) if adt.def_id() == id)
                {
                    c.result.items.insert(impl_id.into());
                    c.result.items.extend(
                        impl_id.impl_items(db).items.iter().map(|(_, item)| AttrDefId::from(*item)),
                    );
                }
            }
        }
        AttrDefId::EnumVariantId(id) => {
            c.result.items.insert(AdtId::from(id.lookup(db).parent).into());
        }
        AttrDefId::TraitId(id) => {
            c.result
                .items
                .extend(id.trait_items(db).items.iter().map(|(_, item)| AttrDefId::from(*item)));
        }
        _ => (),
    }
    if let Some(owner) = body(db, item).filter(|_| initializer) {
        let lowered = Body::of(db, owner);
        let infer = InferenceResult::of(db, owner);
        c.result.unknown |= infer.has_errors;
        for (_, ty) in infer.type_of_expr.iter() {
            ty.as_ref().visit_with(&mut c);
        }
        for (_, ty) in infer.type_of_pat.iter() {
            ty.as_ref().visit_with(&mut c);
        }
        let mut resolver = owner.resolver(db);
        for (expr, value) in lowered.exprs() {
            if let Some((id, args)) = infer.method_resolution(expr) {
                c.function(id, args);
            }
            if let Some((CandidateId::ConstId(id), args)) = infer.assoc_resolutions_for_expr(expr) {
                c.result.items.insert(id.into());
                args.visit_with(&mut c);
            }
            if let Expr::Path(path) = value {
                let guard = resolver.update_to_inner_scope(db, owner, expr);
                match resolver.resolve_path_in_value_ns_fully(
                    db,
                    path,
                    lowered.expr_path_hygiene(expr),
                ) {
                    Some(ValueNs::ConstId(id)) => {
                        c.result.items.insert(id.into());
                    }
                    Some(ValueNs::StaticId(id)) => {
                        c.result.items.insert(id.into());
                    }
                    Some(_) => (),
                    None if infer.assoc_resolutions_for_expr(expr).is_some() => (),
                    None if infer.variant_resolution_for_expr(expr).is_some() => (),
                    None => c.result.unknown = true,
                }
                resolver.reset_to_guard(guard);
            }
        }
        for (pat, value) in lowered.pats() {
            if let Some((CandidateId::ConstId(id), args)) = infer.assoc_resolutions_for_pat(pat) {
                c.result.items.insert(id.into());
                args.visit_with(&mut c);
            } else if matches!(value, Pat::Path(_))
                && infer.variant_resolution_for_pat(pat).is_none()
            {
                c.result.unknown = true;
            }
        }
        let infcx = DbInterner::new_with(db, krate).infer_ctxt().build(TypingMode::PostAnalysis);
        match db.mir_body(owner.into()) {
            Err(_) => c.result.unknown = true,
            Ok(mir) => {
                let mut pending = vec![mir];
                let mut seen_coroutines = FxHashSet::default();
                while let Some(mir) = pending.pop() {
                    for &closure in &mir.closures {
                        match db.mir_body_for_closure(closure) {
                            Ok(body) => pending.push(body),
                            Err(_) => c.result.unknown = true,
                        }
                    }
                    for (_, local) in mir.locals.iter() {
                        local.ty.as_ref().visit_with(&mut c);
                    }
                    for (_, block) in mir.basic_blocks.iter() {
                        for statement in &block.statements {
                            match &statement.kind {
                                StatementKind::Assign(_, value) => match value {
                                    Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => c.operand(op),
                                    Rvalue::Cast(_, op, ty) => {
                                        c.operand(op);
                                        ty.as_ref().visit_with(&mut c);
                                    }
                                    Rvalue::Repeat(op, count) => {
                                        c.operand(op);
                                        count.as_ref().visit_with(&mut c);
                                    }
                                    Rvalue::CheckedBinaryOp(_, a, b) => {
                                        c.operand(a);
                                        c.operand(b);
                                    }
                                    Rvalue::Aggregate(_, ops) => {
                                        for op in ops {
                                            c.operand(op);
                                        }
                                    }
                                    _ => (),
                                },
                                StatementKind::InlineAsm(_) => c.result.unknown = true,
                                _ => (),
                            }
                        }
                        if let Some(term) = &block.terminator {
                            if let TerminatorKind::Drop { place, .. }
                            | TerminatorKind::DropAndReplace { place, .. } = &term.kind
                            {
                                mir.locals[place.local].ty.as_ref().visit_with(&mut c);
                                if !crate::collect_params(&mir.locals[place.local].ty.as_ref())
                                    .is_empty()
                                    && let Some(id) = hir_def::lang_item::lang_items(db, krate).Drop
                                {
                                    c.trait_impls(TraitRef::new(
                                        infcx.interner,
                                        id.into(),
                                        [mir.locals[place.local].ty.as_ref()],
                                    ));
                                }
                            }
                            match &term.kind {
                                TerminatorKind::Call { func, args, .. } => {
                                    let ty = match &func.kind {
                                        OperandKind::Copy(place) | OperandKind::Move(place) => {
                                            place.as_ref().ty(mir, &infcx, env.param_env).ty
                                        }
                                        OperandKind::Constant { ty, .. } => ty.as_ref(),
                                        OperandKind::Allocation { allocation } => {
                                            allocation.as_ref().ty
                                        }
                                        OperandKind::Static(id) => {
                                            db.type_for_static(*id).skip_binder()
                                        }
                                    };
                                    if matches!(ty.kind(), TyKind::FnPtr(..)) {
                                        c.result.unknown = true;
                                    }
                                    ty.visit_with(&mut c);
                                    c.operand(func);
                                    for op in args {
                                        c.operand(op);
                                    }
                                }
                                TerminatorKind::SwitchInt { discr, .. } => c.operand(discr),
                                TerminatorKind::Assert { cond, .. } => c.operand(cond),
                                TerminatorKind::DropAndReplace { value, .. }
                                | TerminatorKind::Yield { value, .. } => c.operand(value),
                                _ => (),
                            }
                        }
                    }
                    for coroutine in c.coroutines.drain() {
                        if seen_coroutines.insert(coroutine) {
                            match db.mir_body_for_coroutine(coroutine) {
                                Ok(body) => pending.push(body),
                                Err(_) => c.result.unknown = true,
                            }
                        }
                    }
                }
            }
        }
    }
    c.result
}

fn module_def(item: ModuleDefId) -> Option<AttrDefId> {
    Some(match item {
        ModuleDefId::ModuleId(id) => id.into(),
        ModuleDefId::FunctionId(id) => id.into(),
        ModuleDefId::AdtId(id) => id.into(),
        ModuleDefId::EnumVariantId(id) => id.into(),
        ModuleDefId::ConstId(id) => id.into(),
        ModuleDefId::StaticId(id) => id.into(),
        ModuleDefId::TraitId(id) => id.into(),
        ModuleDefId::TypeAliasId(id) => id.into(),
        ModuleDefId::MacroId(id) => id.into(),
        ModuleDefId::BuiltinType(_) => return None,
    })
}

fn lexical_source(db: &dyn HirDatabase, item: AttrDefId) -> Option<hir_expand::ErasedAstId> {
    let mut source = hir_def::twins::ast_id(db, item)?;
    for _ in 0..64 {
        let Some(call) = source.file_id.macro_file() else { return Some(source) };
        let kind = &call.loc(db).kind;
        source = hir_expand::ErasedAstId::new(kind.file_id(), kind.erased_ast_id());
    }
    None
}

fn macro_escapes(db: &dyn HirDatabase, normal: Crate, test: Crate, item: AttrDefId) -> bool {
    let AttrDefId::MacroId(id) = item else { return false };
    if AttrFlags::query(db, item).contains(AttrFlags::IS_MACRO_EXPORT) {
        return true;
    }
    let Some(source) = lexical_source(db, item) else { return true };
    let end = source.to_ptr(db).text_range().end();
    let twins = twin_index(db, normal, test);
    for (_, module) in scope_pairs(db, normal, test) {
        let scope = module.def_map(db).module(db, module).scope(db);
        if scope.macros().any(|(_, entry)| entry.def == id) {
            return true;
        }
        if !scope.legacy_macros().any(|(_, macros)| macros.contains(&id)) {
            continue;
        }
        for &common in twins.twins.keys() {
            let owner = common.module(db);
            if owner != module
                && !matches!(common, AttrDefId::ModuleId(child) if child.containing_module(db) == Some(module))
            {
                continue;
            }
            let Some(common) = lexical_source(db, common) else { return true };
            if common.file_id != source.file_id || common.to_ptr(db).text_range().start() >= end {
                return true;
            }
        }
    }
    false
}

#[salsa::tracked(returns(ref))]
pub fn pair_safety(db: &dyn HirDatabase, normal: Crate, test: Crate) -> Vec<&'static str> {
    let mut veto = FxHashSet::default();
    let twins = twin_index(db, normal, test);
    let nitems = crate_items(db, normal);
    let titems = crate_items(db, test);
    for (&def, &item) in &titems.definitions {
        if matches!(def.kind, hir_expand::MacroDefKind::Declarative(..))
            && item.module(db).krate(db) == test
            && hir_def::twins::gated_off(db, item, normal.cfg_options(db))
            && macro_escapes(db, normal, test, item)
        {
            veto.insert("cfg-test-macro-rules");
        }
    }
    for (n, t) in scope_pairs(db, normal, test) {
        let ns = n.def_map(db).module(db, n).scope(db);
        let ts = t.def_map(db).module(db, t).scope(db);
        for (name, entry) in ts.entries() {
            let own = ns.get(name);
            let resolved = n.resolver(db).resolve_module_path_in_items(
                db,
                &ModPath::from_segments(PathKind::Plain, [name.clone()]),
            );
            for (target, prior, found) in [
                (
                    entry.types.map(|i| i.def),
                    own.types.filter(|i| i.import.is_none()).map(|i| i.def),
                    resolved.types.map(|i| i.def),
                ),
                (
                    entry.values.map(|i| i.def),
                    own.values.filter(|i| i.import.is_none()).map(|i| i.def),
                    resolved.values.map(|i| i.def),
                ),
                (
                    entry.macros.map(|i| i.def.into()),
                    own.macros.filter(|i| i.import.is_none()).map(|i| i.def.into()),
                    resolved.macros.map(|i| i.def.into()),
                ),
            ] {
                if let (Some(target), None, Some(found)) = (target, prior, found) {
                    let mapped = module_def(target).and_then(|id| twins.twins.get(&id).copied());
                    if target != found && (mapped.is_none() || mapped != module_def(found)) {
                        veto.insert("namespace-shadowing");
                    }
                }
            }
        }
    }
    for &item in &titems.items {
        let AttrDefId::ImplId(id) = item else { continue };
        if twins.twins.contains_key(&item) {
            if twins.cfg_differing_items.contains(&item) || twins.unknown_items.contains(&item) {
                veto.insert("impl-cfg-unknown");
            }
            continue;
        }
        let self_ty = db.impl_self_ty(id).skip_binder();
        let self_adt = match self_ty.kind() {
            TyKind::Adt(adt, _) => Some(adt.def_id()),
            _ => None,
        };
        let only_self = self_adt.is_some_and(|adt| twins.test_only.contains(&adt.into()));
        if ImplSignature::of(db, id).target_trait.is_some() && db.impl_trait(id).is_none() {
            veto.insert("impl-trait-unknown");
        } else if let Some(tr) = db.impl_trait(id) {
            if !crate::collect_params(&self_ty).is_empty() {
                veto.insert("test-only-blanket-impl");
            } else if !only_self && !twins.test_only.contains(&tr.skip_binder().def_id.0.into()) {
                veto.insert("test-only-trait-impl");
            }
        } else if !only_self {
            let methods: FxHashSet<_> = id
                .impl_items(db)
                .items
                .iter()
                .filter_map(|(name, item)| {
                    matches!(item, hir_def::AssocItemId::FunctionId(_)).then_some(name)
                })
                .collect();
            for &n in &nitems.items {
                let AttrDefId::ImplId(n) = n else { continue };
                if db.impl_trait(n).is_some() {
                    continue;
                }
                let nself = db.impl_self_ty(n).skip_binder();
                let same = match (nself.kind(), self_adt) {
                    (TyKind::Adt(adt, _), Some(tadt)) => {
                        twins.twins.get(&tadt.into()) == Some(&adt.def_id().into())
                    }
                    (_, None) => nself == self_ty,
                    _ => false,
                };
                if same && n.impl_items(db).items.iter().any(|(name, _)| methods.contains(name)) {
                    veto.insert("colliding-inherent-method");
                }
            }
        }
    }
    let mut veto: Vec<_> = veto.into_iter().collect();
    veto.sort_unstable();
    veto
}

fn same_static_type(
    db: &dyn HirDatabase,
    normal: Crate,
    n: hir_def::StaticId,
    t: hir_def::StaticId,
    twins: &FxHashMap<AttrDefId, AttrDefId>,
) -> bool {
    struct MapTypes<'a, 'db> {
        interner: DbInterner<'db>,
        twins: &'a FxHashMap<AttrDefId, AttrDefId>,
    }
    impl<'db> TypeFolder<DbInterner<'db>> for MapTypes<'_, 'db> {
        fn cx(&self) -> DbInterner<'db> {
            self.interner
        }
        fn fold_ty(&mut self, ty: Ty<'db>) -> Ty<'db> {
            if let TyKind::Adt(adt, args) = ty.kind()
                && let Some(AttrDefId::AdtId(n)) = self.twins.get(&adt.def_id().into())
            {
                return Ty::new_adt(self.interner, *n, args.fold_with(self));
            }
            ty.super_fold_with(self)
        }
    }
    let interner = DbInterner::new_with(db, normal);
    let n = db.type_for_static(n).skip_binder();
    let t = db.type_for_static(t).skip_binder().fold_with(&mut MapTypes { interner, twins });
    !n.references_error() && !t.references_error() && !n.has_non_region_infer() && n == t
}

#[salsa::tracked(returns(ref))]
pub fn pair_eligibility(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    both: bool,
) -> Eligibility {
    let twins = twin_index(db, normal, test);
    let mut result = Eligibility {
        pair_veto: pair_safety(db, normal, test).clone(),
        test_only_statics: twins
            .test_only
            .iter()
            .filter(|item| matches!(item, AttrDefId::StaticId(_)))
            .count(),
        ..Eligibility::default()
    };
    let mut graph = DiGraph::<AttrDefId, ()>::new();
    let nodes: FxHashMap<_, _> =
        crate_items(db, normal).items.iter().map(|&item| (item, graph.add_node(item))).collect();
    let matched: FxHashMap<_, _> = twins.twins.iter().map(|(&t, &n)| (n, t)).collect();
    let per_copy: FxHashSet<_> = matched
        .iter()
        .filter_map(|(&n, &t)| {
            let (AttrDefId::StaticId(n), AttrDefId::StaticId(t)) = (n, t) else { return None };
            same_static_type(db, normal, n, t, &twins.twins).then_some(AttrDefId::from(n))
        })
        .collect();
    let mut own = FxHashMap::default();
    for (&item, &node) in &nodes {
        let refs = references(db, item, !per_copy.contains(&item));
        let reason = if let Some(&t) = matched.get(&item) {
            if !per_copy.contains(&item) && twins.cfg_differing_items.contains(&t) {
                Some(Rejection::CfgDiffering)
            } else if !per_copy.contains(&item) && twins.unknown_items.contains(&t) {
                Some(Rejection::Unknown)
            } else if refs.generic_unresolved {
                Some(Rejection::GenericUnresolved)
            } else if refs.unknown {
                Some(Rejection::Unknown)
            } else {
                None
            }
        } else {
            Some(Rejection::Transitive)
        };
        if matches!(item, AttrDefId::StaticId(_)) {
            result.statics += 1;
        }
        if let Some(reason) = reason {
            own.insert(node, reason);
        }
        for target in &refs.items {
            if let Some(&target) = nodes.get(target) {
                graph.add_edge(node, target, ());
            } else if target.module(db).krate(db) == normal {
                own.entry(node).or_insert(Rejection::Transitive);
            }
        }
    }
    let rejected = reverse_closure(&graph, own.keys().copied());
    let static_closure = reverse_closure(
        &graph,
        nodes.iter().filter_map(|(item, &node)| {
            (both && matches!(item, AttrDefId::StaticId(_))).then_some(node)
        }),
    );
    for (&n, &t) in &matched {
        let node = nodes[&n];
        let reason = own
            .get(&node)
            .copied()
            .filter(|reason| *reason == Rejection::CfgDiffering || twins.unknown_items.contains(&t))
            .or_else(|| {
                if let Some(reason) = own.get(&node).copied() {
                    Some(reason)
                } else if rejected.contains(&node) {
                    Some(Rejection::Transitive)
                } else {
                    None
                }
            });
        if let Some(reason) = reason {
            result.rejected.insert(t, reason);
        } else if static_closure.contains(&node) {
            result.analysis_shared.insert(t);
        } else {
            result.candidates.insert(t);
        }
    }
    result
}

fn reverse_closure<N>(
    graph: &DiGraph<N, ()>,
    seeds: impl IntoIterator<Item = petgraph::graph::NodeIndex>,
) -> FxHashSet<petgraph::graph::NodeIndex> {
    let components = kosaraju_scc(graph);
    let mut component = FxHashMap::default();
    for (id, nodes) in components.iter().enumerate() {
        for &node in nodes {
            component.insert(node, id);
        }
    }
    let mut rejected = vec![false; components.len()];
    let mut reverse = vec![Vec::new(); components.len()];
    for edge in graph.raw_edges() {
        reverse[component[&edge.target()]].push(component[&edge.source()]);
    }
    for node in seeds {
        rejected[component[&node]] = true;
    }
    let mut pending: VecDeque<_> =
        rejected.iter().enumerate().filter_map(|(id, &set)| set.then_some(id)).collect();
    while let Some(id) = pending.pop_front() {
        for &parent in &reverse[id] {
            if !rejected[parent] {
                rejected[parent] = true;
                pending.push_back(parent);
            }
        }
    }
    graph.node_indices().filter(|node| rejected[component[node]]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_candidates_survive_without_an_ineligible_dependency() {
        let mut graph = DiGraph::new();
        let a = graph.add_node(());
        let b = graph.add_node(());
        let independent = graph.add_node(());
        graph.add_edge(a, b, ());
        graph.add_edge(b, a, ());
        assert!(reverse_closure(&graph, []).is_empty());
        assert_eq!(reverse_closure(&graph, [independent]), FxHashSet::from_iter([independent]));
    }

    #[test]
    fn ineligible_dependency_removes_the_scc_and_its_callers() {
        let mut graph = DiGraph::new();
        let caller = graph.add_node(());
        let a = graph.add_node(());
        let b = graph.add_node(());
        let dependency = graph.add_node(());
        let independent = graph.add_node(());
        graph.add_edge(caller, a, ());
        graph.add_edge(a, b, ());
        graph.add_edge(b, a, ());
        graph.add_edge(b, dependency, ());
        let rejected = reverse_closure(&graph, [dependency]);
        assert_eq!(rejected, FxHashSet::from_iter([caller, a, b, dependency]));
        assert!(!rejected.contains(&independent));
    }

    #[test]
    fn empty_graph_has_no_rejections() {
        assert!(reverse_closure(&DiGraph::<(), ()>::new(), []).is_empty());
    }
}
