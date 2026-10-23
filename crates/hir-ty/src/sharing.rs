//! Eligibility for sharing analysis and codegen between normal and test crates.
//!
//! The reference inventory follows rustc's `MirNeighborCollector` in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_monomorphize/src/collector.rs>:
//! function operands, constants, statics, drops and unsizing can introduce code dependencies.
//! Concrete calls use the selected impl; unresolved dispatch and vtables retain
//! local impls whose instantiated trait arguments can unify. `pair_safety` must hold
//! before using either sharing class.
//! ADT impl compatibility follows freshened impl-header comparison in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_trait_selection/src/traits/coherence.rs>:
//! retain possible overlaps without proving where-clauses.
//! Textual macro escape follows `define_macro` and module visitation in
//! `rustc_resolve/src/build_reduced_graph.rs` at the same rustc tag.
//! Local reuse preserves definition identity, as do rustc's `typeck` and `mir_built`
//! queries in `compiler/rustc_middle/src/query/mod.rs` at that tag; only analysis
//! results are remapped. Declaration matching is independent of body inventories.

use std::{
    collections::VecDeque,
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

use base_db::Crate;
use hir_def::{
    AdtId, AttrDefId, CallableDefId, DefWithBodyId, FunctionId, GenericDefId, HasModule, ImplId,
    ItemContainerId, Lookup, ModuleDefId, TraitId, VariantId,
    attrs::AttrFlags,
    expr_store::{Body, ExpressionStore, HygieneId, StoreVisitor},
    hir::{Array, Expr, ExprId, Pat, generics::GenericParams},
    resolver::{HasResolver, ValueNs},
    signatures::{ConstSignature, FunctionSignature, ImplSignature, TypeAliasSignature},
    twins::{crate_items, scope_pairs, twin_index},
    type_ref::{TypeRef, TypeRefId},
};
use hir_expand::mod_path::{ModPath, PathKind};
use petgraph::{algo::kosaraju_scc, graph::DiGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{
    TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable,
    TypeVisitableExt, TypeVisitor,
    inherent::{GenericArgs as _, IntoKind},
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalRejection {
    CfgDiffering,
    Unknown,
    PairSafety,
    MissingTwin,
    Signature,
    ImplMismatch,
    BakedValue,
}

impl LocalRejection {
    pub fn class(self) -> &'static str {
        match self {
            Self::CfgDiffering => "cfg-differing",
            Self::Unknown => "unknown",
            Self::PairSafety => "separate(pair-safety)",
            Self::MissingTwin => "separate(missing-twin)",
            Self::Signature => "separate(signature)",
            Self::ImplMismatch => "separate(impl-mismatch)",
            Self::BakedValue => "separate(baked-value)",
        }
    }
}

static LOCAL_TIMES: [AtomicU64; 3] = [const { AtomicU64::new(0) }; 3];

fn local_time<T>(phase: usize, work: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let result = work();
    LOCAL_TIMES[phase].fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
    result
}

pub fn take_local_times() -> [Duration; 3] {
    LOCAL_TIMES.each_ref().map(|time| Duration::from_nanos(time.swap(0, Ordering::Relaxed)))
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Eligibility {
    /// Fully shareable T items before the crate-wide safety veto.
    pub candidates: FxHashSet<AttrDefId>,
    pub analysis_shared: FxHashSet<AttrDefId>,
    pub rejected: FxHashMap<AttrDefId, Rejection>,
    pub pair_veto: Vec<&'static str>,
    pub statics: usize,
    pub test_only_statics: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct References {
    items: FxHashSet<AttrDefId>,
    type_items: FxHashSet<AttrDefId>,
    signature_types: FxHashSet<AttrDefId>,
    baked_items: FxHashSet<AttrDefId>,
    unknown: bool,
    generic_unresolved: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodySharingFacts {
    references: Option<References>,
    cfg: cfg::CfgReads,
    items: BodyItems,
}

impl BodySharingFacts {
    pub fn changed_fields(&self, new: &Self) -> Vec<(&'static str, String, String)> {
        let mut changed = Vec::new();
        macro_rules! field {
            ($name:literal, $old:expr, $new:expr) => {
                if $old != $new {
                    changed.push(($name, format!("{:?}", $old), format!("{:?}", $new)));
                }
            };
        }
        match (&self.references, &new.references) {
            (Some(old), Some(new)) => {
                field!("references.items", old.items, new.items);
                field!("references.type_items", old.type_items, new.type_items);
                field!("references.signature_types", old.signature_types, new.signature_types);
                field!("references.baked_items", old.baked_items, new.baked_items);
                field!("references.unknown", old.unknown, new.unknown);
                field!(
                    "references.generic_unresolved",
                    old.generic_unresolved,
                    new.generic_unresolved
                );
            }
            (old, new) => field!("references", old, new),
        }
        field!("cfg.atoms", self.cfg.atoms, new.cfg.atoms);
        field!("cfg.predicates", self.cfg.predicates, new.cfg.predicates);
        field!("cfg.read_all", self.cfg.read_all, new.cfg.read_all);
        field!("cfg.unknown", self.cfg.unknown, new.cfg.unknown);
        field!("items.declarations", self.items.declarations, new.items.declarations);
        field!("items.impls", self.items.impls, new.items.impls);
        field!("items.macros", self.items.macros, new.items.macros);
        changed
    }
}

#[cfg(test)]
mod body_fact_tests {
    use super::{
        BodyItems, BodySharingFacts, LocalRejection, References, Rejection, local_own_reason,
    };

    #[test]
    fn local_sharing_rejects_only_body_local_facts() {
        assert_eq!(local_own_reason(None), None);
        assert_eq!(local_own_reason(Some(Rejection::GenericUnresolved)), None);
        assert_eq!(local_own_reason(Some(Rejection::Transitive)), None);
        assert_eq!(
            local_own_reason(Some(Rejection::CfgDiffering)),
            Some(LocalRejection::CfgDiffering)
        );
        assert_eq!(local_own_reason(Some(Rejection::Unknown)), Some(LocalRejection::Unknown));
        assert_eq!(LocalRejection::BakedValue.class(), "separate(baked-value)");
        assert_eq!(LocalRejection::MissingTwin.class(), "separate(missing-twin)");
    }

    #[test]
    fn identifies_changed_fields_without_position_data() {
        let old = BodySharingFacts {
            references: Some(References::default()),
            cfg: Default::default(),
            items: BodyItems::default(),
        };
        assert!(old.changed_fields(&old).is_empty());
        let mut new = old.clone();
        new.references.as_mut().unwrap().unknown = true;
        new.cfg.unknown = true;
        assert_eq!(
            old.changed_fields(&new),
            vec![
                ("references.unknown", "false".into(), "true".into()),
                ("cfg.unknown", "false".into(), "true".into()),
            ]
        );
        new = old.clone();
        new.references = None;
        assert_eq!(old.changed_fields(&new)[0].0, "references");
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BodyItems {
    declarations: Vec<ModuleDefId>,
    impls: Vec<ImplId>,
    macros: Vec<hir_def::MacroId>,
}

#[salsa::tracked(returns(ref))]
pub fn body_item_inventory(db: &dyn HirDatabase, func: FunctionId) -> BodyItems {
    let mut items = BodyItems::default();
    for (_, map) in Body::of(db, func.into()).blocks(db) {
        for (_, module) in map.modules(db) {
            let scope = module.scope(db);
            items.declarations.extend(scope.declarations());
            items.declarations.extend(scope.unnamed_consts().map(ModuleDefId::ConstId));
            items.impls.extend(scope.impls());
            items.macros.extend(
                scope
                    .legacy_macros()
                    .flat_map(|(_, ids)| ids.iter().copied())
                    .chain(scope.macros().map(|(_, item)| item.def)),
            );
        }
    }
    items
}

#[salsa::tracked(returns(ref))]
pub fn body_sharing_facts(
    db: &dyn HirDatabase,
    func: FunctionId,
    normal: bool,
) -> BodySharingFacts {
    BodySharingFacts {
        references: normal.then(|| references(db, func.into(), true).clone()),
        cfg: Body::cfg_reads(db, func.into()).clone(),
        items: body_item_inventory(db, func).clone(),
    }
}

struct Collector<'db> {
    db: &'db dyn HirDatabase,
    krate: Crate,
    env: ParamEnvAndCrate<'db>,
    result: References,
    seen: FxHashSet<Ty<'db>>,
    traits: FxHashSet<TraitRef<'db>>,
    coroutines: FxHashSet<crate::db::InternedCoroutineId<'db>>,
    type_depth: usize,
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
fn local_impls(db: &dyn HirDatabase, krate: Crate) -> FxHashSet<ImplId> {
    crate_items(db, krate)
        .items
        .iter()
        .filter_map(|item| match item {
            AttrDefId::ImplId(id) => Some(*id),
            _ => None,
        })
        .collect()
}

#[salsa::tracked(returns(ref))]
fn local_trait_impls(db: &dyn HirDatabase, krate: Crate) -> FxHashMap<TraitId, Vec<ImplId>> {
    let mut result: FxHashMap<TraitId, Vec<ImplId>> = FxHashMap::default();
    for &id in local_impls(db, krate) {
        if let Some(tr) = db.impl_trait(id) {
            result.entry(tr.skip_binder().def_id.0).or_default().push(id);
        }
    }
    result
}

#[salsa::tracked(returns(ref))]
fn applicable_adt_impls(db: &dyn HirDatabase, adt: AdtId) -> FxHashSet<ImplId> {
    struct MentionsAdt {
        adt: AdtId,
        found: bool,
    }
    impl<'db> TypeVisitor<DbInterner<'db>> for MentionsAdt {
        type Result = ();
        fn visit_ty(&mut self, ty: Ty<'db>) {
            self.found |= matches!(ty.kind(), TyKind::Adt(def, _) if def.def_id() == self.adt);
            ty.super_visit_with(self);
        }
    }
    let krate = adt.module(db).krate(db);
    let mut infcx = DbInterner::new_with(db, krate).infer_ctxt().build(TypingMode::PostAnalysis);
    let mut result = FxHashSet::default();
    for &id in local_impls(db, krate) {
        let mut mentions = MentionsAdt { adt, found: false };
        db.impl_self_ty(id).skip_binder().visit_with(&mut mentions);
        if let Some(trait_ref) = db.impl_trait(id) {
            trait_ref.skip_binder().visit_with(&mut mentions);
        }
        let args = GenericArgs::identity_for_item(infcx.interner, id.into());
        for clause in GenericPredicates::query_all(db, id.into())
            .iter_instantiated(infcx.interner, args.as_slice())
        {
            clause.skip_norm_wip().visit_with(&mut mentions);
        }
        if mentions.found {
            result.insert(id);
            continue;
        }
        match db.impl_self_ty(id).skip_binder().kind() {
            TyKind::Adt(def, _) if def.def_id() != adt => continue,
            TyKind::Adt(..) | TyKind::Param(..) | TyKind::Alias(..) | TyKind::Error(..) => {}
            _ => continue,
        }
        if infcx.probe(|_| {
            let target_args = infcx.fresh_args_for_item(Span::Dummy, adt.into());
            let target = Ty::new_adt(infcx.interner, adt, target_args);
            let args = infcx.fresh_args_for_item(Span::Dummy, id.into());
            let candidate = db.impl_self_ty(id).instantiate(infcx.interner, args).skip_norm_wip();
            let candidate = candidate.fold_with(&mut CandidateArgs {
                infcx: &infcx,
                types: FxHashMap::default(),
                consts: FxHashMap::default(),
            });
            infcx
                .at(&ObligationCause::dummy(), crate::next_solver::ParamEnv::empty())
                .eq(target, candidate)
                .is_ok()
        }) {
            result.insert(id);
        }
    }
    result
}

fn same_impl_items(
    db: &dyn HirDatabase,
    normal: ImplId,
    test: ImplId,
    twins: &FxHashMap<AttrDefId, AttrDefId>,
) -> bool {
    let normal: FxHashSet<_> =
        normal.impl_items(db).items.iter().map(|(_, id)| AttrDefId::from(*id)).collect();
    let test = test.impl_items(db);
    test.items.len() == normal.len()
        && test
            .items
            .iter()
            .all(|(_, id)| twins.get(&AttrDefId::from(*id)).is_some_and(|id| normal.contains(id)))
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
        self.type_depth += 1;
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                self.result.type_items.insert(adt.def_id().into());
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
        self.type_depth -= 1;
    }

    fn visit_const(&mut self, konst: Const<'db>) {
        if self.type_depth != 0
            && let ConstKind::Unevaluated(uv) = konst.kind()
        {
            match uv.def.0 {
                GeneralConstId::ConstId(id) => {
                    self.result.type_items.insert(id.into());
                }
                GeneralConstId::StaticId(id) => {
                    self.result.type_items.insert(id.into());
                }
                GeneralConstId::AnonConstId(_) => self.result.unknown = true,
            }
        }
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
        type_depth: 0,
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
                        c.result.type_items.insert((*id).into());
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
    c.result.signature_types = c.result.type_items.clone();
    if let Some(owner) = body(db, item).filter(|_| initializer) {
        let lowered = Body::of(db, owner);
        let baked = baked_expressions(&lowered);
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
            let guard = resolver.update_to_inner_scope(db, owner, expr);
            for path in baked_type_paths(&lowered, expr) {
                if let Some(ValueNs::ConstId(id)) =
                    resolver.resolve_path_in_value_ns_fully(db, &path, HygieneId::ROOT)
                {
                    c.result.items.insert(id.into());
                    c.result.baked_items.insert(id.into());
                }
            }
            if let Some((id, args)) = infer.method_resolution(expr) {
                c.function(id, args);
                if baked.contains(&expr) {
                    c.result.baked_items.insert(id.into());
                }
            }
            if let Some((CandidateId::ConstId(id), args)) = infer.assoc_resolutions_for_expr(expr) {
                c.result.items.insert(id.into());
                if baked.contains(&expr) {
                    c.result.baked_items.insert(id.into());
                }
                args.visit_with(&mut c);
            }
            if let Expr::Path(path) = value {
                match resolver.resolve_path_in_value_ns_fully(
                    db,
                    path,
                    lowered.expr_path_hygiene(expr),
                ) {
                    Some(ValueNs::ConstId(id)) => {
                        c.result.items.insert(id.into());
                        if baked.contains(&expr) {
                            c.result.baked_items.insert(id.into());
                        }
                    }
                    Some(ValueNs::FunctionId(id)) if baked.contains(&expr) => {
                        c.result.baked_items.insert(id.into());
                    }
                    Some(ValueNs::StaticId(id)) => {
                        c.result.items.insert(id.into());
                    }
                    Some(_) => (),
                    None if infer.assoc_resolutions_for_expr(expr).is_some() => (),
                    None if infer.variant_resolution_for_expr(expr).is_some() => (),
                    None => c.result.unknown = true,
                }
            }
            resolver.reset_to_guard(guard);
        }
        for (pat, value) in lowered.pats() {
            if let Some((CandidateId::ConstId(id), args)) = infer.assoc_resolutions_for_pat(pat) {
                c.result.items.insert(id.into());
                c.result.baked_items.insert(id.into());
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

fn macro_escapes(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    item: AttrDefId,
    local: bool,
) -> bool {
    let AttrDefId::MacroId(id) = item else { return false };
    if AttrFlags::query(db, item).contains(AttrFlags::IS_MACRO_EXPORT) {
        return true;
    }
    let Some(source) = lexical_source(db, item) else { return true };
    let end = source.to_ptr(db).text_range().end();
    let twins: Vec<_> = if local {
        hir_def::twins::declaration_items(db, test)
            .items
            .iter()
            .copied()
            .filter(|&item| hir_def::twins::declaration_twin(db, normal, test, item).is_some())
            .collect()
    } else {
        twin_index(db, normal, test).twins.keys().copied().collect()
    };
    for (_, module) in safety_scopes(db, normal, test, local) {
        let scope = module.def_map(db).module(db, module).scope(db);
        if scope.macros().any(|(_, entry)| entry.def == id) {
            return true;
        }
        if !scope.legacy_macros().any(|(_, macros)| macros.contains(&id)) {
            continue;
        }
        for &common in &twins {
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
    pair_safety_mode(db, normal, test, false)
}

#[salsa::tracked(returns(ref))]
pub fn local_pair_safety(db: &dyn HirDatabase, normal: Crate, test: Crate) -> Vec<&'static str> {
    pair_safety_mode(db, normal, test, true)
}

fn safety_scopes(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    local: bool,
) -> Vec<(hir_def::ModuleId, hir_def::ModuleId)> {
    if local {
        hir_def::twins::declaration_scope_pairs(db, normal, test)
    } else {
        scope_pairs(db, normal, test)
    }
}

fn safety_items(db: &dyn HirDatabase, krate: Crate, local: bool) -> &hir_def::twins::CrateItems {
    if local { hir_def::twins::declaration_items(db, krate) } else { crate_items(db, krate) }
}

fn safety_twin(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    item: AttrDefId,
    local: bool,
) -> Option<AttrDefId> {
    if local {
        hir_def::twins::declaration_twin(db, normal, test, item)
    } else {
        twin_index(db, normal, test).twins.get(&item).copied()
    }
}

fn pair_safety_mode(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    local: bool,
) -> Vec<&'static str> {
    let mut veto = FxHashSet::default();
    let titems = safety_items(db, test, local);
    for (&def, &item) in &titems.definitions {
        if matches!(def.kind, hir_expand::MacroDefKind::Declarative(..))
            && item.module(db).krate(db) == test
            && test_macro_escapes(db, normal, test, item, local)
        {
            veto.insert("cfg-test-macro-rules");
        }
    }
    for (n, t) in safety_scopes(db, normal, test, local) {
        if namespace_shadowed(db, normal, test, n, t, local) {
            veto.insert("namespace-shadowing");
        }
    }
    veto.extend(impl_safety(db, normal, test, local));
    let mut veto: Vec<_> = veto.into_iter().collect();
    veto.sort_unstable();
    veto
}

#[salsa::tracked(returns(copy))]
fn namespace_shadowed(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    n: hir_def::ModuleId,
    t: hir_def::ModuleId,
    local: bool,
) -> bool {
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
                let mapped =
                    module_def(target).and_then(|id| safety_twin(db, normal, test, id, local));
                if target != found && (mapped.is_none() || mapped != module_def(found)) {
                    return true;
                }
            }
        }
    }
    false
}

#[salsa::tracked(returns(clone))]
fn impl_safety(db: &dyn HirDatabase, normal: Crate, test: Crate, local: bool) -> Vec<&'static str> {
    let mut veto = FxHashSet::default();
    let nitems = safety_items(db, normal, local);
    let titems = safety_items(db, test, local);
    for &item in &titems.items {
        let AttrDefId::ImplId(id) = item else { continue };
        if safety_twin(db, normal, test, item, local).is_some() {
            let bad = if local {
                let reads = hir_def::twins::declaration_reads(db, item);
                reads.unknown
                    || reads.differs_from(normal.cfg_options(db))
                    || safety_twin(db, normal, test, item, local).is_some_and(|normal_item| {
                        let reads = hir_def::twins::declaration_reads(db, normal_item);
                        reads.unknown || reads.differs_from(test.cfg_options(db))
                    })
            } else {
                let twins = twin_index(db, normal, test);
                twins.cfg_differing_items.contains(&item) || twins.unknown_items.contains(&item)
            };
            if bad {
                veto.insert("impl-cfg-unknown");
            }
            continue;
        }
        let self_ty = db.impl_self_ty(id).skip_binder();
        let self_adt = match self_ty.kind() {
            TyKind::Adt(adt, _) => Some(adt.def_id()),
            _ => None,
        };
        let only_self = self_adt
            .is_some_and(|adt| hir_def::twins::gated_off(db, adt.into(), normal.cfg_options(db)));
        if ImplSignature::of(db, id).target_trait.is_some() && db.impl_trait(id).is_none() {
            veto.insert("impl-trait-unknown");
        } else if let Some(tr) = db.impl_trait(id) {
            if !crate::collect_params(&self_ty).is_empty() {
                veto.insert("test-only-blanket-impl");
            } else if !only_self
                && !hir_def::twins::gated_off(
                    db,
                    tr.skip_binder().def_id.0.into(),
                    normal.cfg_options(db),
                )
            {
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
                        safety_twin(db, normal, test, tadt.into(), local)
                            == Some(adt.def_id().into())
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

#[salsa::tracked(returns(copy))]
fn test_macro_escapes(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    item: AttrDefId,
    local: bool,
) -> bool {
    hir_def::twins::gated_off(db, item, normal.cfg_options(db))
        && macro_escapes(db, normal, test, item, local)
}

#[salsa::tracked(returns(ref))]
fn generic_twins(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
) -> FxHashMap<GenericDefId, GenericDefId> {
    twin_index(db, normal, test)
        .twins
        .iter()
        .filter_map(|(&t, &n)| Some((generic(t)?, generic(n)?)))
        .collect()
}

#[salsa::tracked]
fn same_signature(db: &dyn HirDatabase, normal: Crate, n: AttrDefId, t: AttrDefId) -> bool {
    *same_signature_mode(db, normal, n, t, false)
}

#[salsa::tracked]
fn same_signature_mode(
    db: &dyn HirDatabase,
    normal: Crate,
    n: AttrDefId,
    t: AttrDefId,
    local: bool,
) -> bool {
    let test = t.module(db).krate(db);
    let twins = (!local).then(|| &twin_index(db, normal, test).twins);
    struct MapTypes<'a, 'db> {
        interner: DbInterner<'db>,
        twins: Option<&'a FxHashMap<AttrDefId, AttrDefId>>,
        generics: Option<&'a FxHashMap<GenericDefId, GenericDefId>>,
        normal: Crate,
        test: Crate,
    }
    impl MapTypes<'_, '_> {
        fn item(&self, item: AttrDefId) -> Option<AttrDefId> {
            if item.module(self.interner.db()).krate(self.interner.db()) != self.test {
                return None;
            }
            match self.twins {
                Some(twins) => twins.get(&item).copied(),
                None => hir_def::twins::declaration_twin(
                    self.interner.db(),
                    self.normal,
                    self.test,
                    item,
                ),
            }
        }
        fn parent(&self, parent: GenericDefId) -> Option<GenericDefId> {
            if let Some(generics) = self.generics {
                return generics.get(&parent).copied();
            }
            let item = match parent {
                GenericDefId::AdtId(id) => id.into(),
                GenericDefId::ConstId(id) => id.into(),
                GenericDefId::FunctionId(id) => id.into(),
                GenericDefId::ImplId(id) => id.into(),
                GenericDefId::StaticId(id) => id.into(),
                GenericDefId::TraitId(id) => id.into(),
                GenericDefId::TypeAliasId(id) => id.into(),
            };
            generic(self.item(item)?)
        }
    }
    impl<'db> TypeFolder<DbInterner<'db>> for MapTypes<'_, 'db> {
        fn cx(&self) -> DbInterner<'db> {
            self.interner
        }
        fn fold_region(
            &mut self,
            region: crate::next_solver::Region<'db>,
        ) -> crate::next_solver::Region<'db> {
            use crate::next_solver::{BoundRegionKind, Region, RegionKind};
            match region.kind() {
                RegionKind::ReEarlyParam(mut param) => {
                    if let Some(parent) = self.parent(param.id.parent) {
                        param.id.parent = parent;
                    }
                    Region::new_early_param(self.interner, param)
                }
                RegionKind::ReBound(index, mut bound) => {
                    if matches!(bound.kind, BoundRegionKind::Named(_)) {
                        bound.kind = BoundRegionKind::Anon;
                    }
                    Region::new(self.interner, RegionKind::ReBound(index, bound))
                }
                _ => region,
            }
        }
        fn fold_const(&mut self, value: Const<'db>) -> Const<'db> {
            if let ConstKind::Param(mut p) = value.kind()
                && let Some(parent) = self.parent(p.id.parent())
            {
                p.id = hir_def::ConstParamId::from_unchecked(hir_def::TypeOrConstParamId {
                    parent,
                    local_id: p.id.local_id(),
                });
                return Const::new_param(self.interner, p);
            }
            value.super_fold_with(self)
        }
        fn fold_ty(&mut self, ty: Ty<'db>) -> Ty<'db> {
            if let TyKind::Param(p) = ty.kind()
                && let Some(parent) = self.parent(p.id.parent())
            {
                let id = hir_def::TypeParamId::from_unchecked(hir_def::TypeOrConstParamId {
                    parent,
                    local_id: p.id.local_id(),
                });
                return Ty::new_param(self.interner, id, p.index);
            }
            if let TyKind::Alias(alias) = ty.kind()
                && let AliasTyKind::Opaque { def_id } = alias.kind
            {
                let loc = match def_id.0.loc(self.interner.db()) {
                    crate::ImplTraitId::ReturnTypeImplTrait(f, idx) => {
                        self.item(f.into()).and_then(|id| match id {
                            AttrDefId::FunctionId(f) => {
                                Some(crate::ImplTraitId::ReturnTypeImplTrait(f, idx))
                            }
                            _ => None,
                        })
                    }
                    crate::ImplTraitId::TypeAliasImplTrait(a, idx) => {
                        self.item(a.into()).and_then(|id| match id {
                            AttrDefId::TypeAliasId(a) => {
                                Some(crate::ImplTraitId::TypeAliasImplTrait(a, idx))
                            }
                            _ => None,
                        })
                    }
                };
                if let Some(loc) = loc {
                    return Ty::new_opaque(
                        self.interner,
                        crate::db::InternedOpaqueTyId::new(self.interner.db(), loc),
                        alias.args.fold_with(self),
                    );
                }
            }
            if let TyKind::Adt(adt, args) = ty.kind()
                && let Some(AttrDefId::AdtId(n)) = self.item(adt.def_id().into())
            {
                return Ty::new_adt(self.interner, n, args.fold_with(self));
            }
            ty.super_fold_with(self)
        }
    }
    let interner = DbInterner::new_with(db, normal);
    let generics = (!local).then(|| generic_twins(db, normal, test));
    let mut mapper = MapTypes { interner, twins, generics, normal, test };
    match (n, t) {
        (AttrDefId::FunctionId(n), AttrDefId::FunctionId(t)) => {
            let reads = hir_def::twins::item_cfg_reads(db, n.into());
            if reads.unknown || reads.differs_from(t.krate(db).cfg_options(db)) {
                return false;
            }
            let generics_match =
                GenericParams::of(db, n.into()).len() == GenericParams::of(db, t.into()).len();
            let n = db.callable_item_signature(n.into()).skip_binder().fold_with(&mut mapper);
            let t = db.callable_item_signature(t.into()).skip_binder().fold_with(&mut mapper);
            generics_match && !n.has_non_region_error() && !t.has_non_region_error() && n == t
        }
        (AttrDefId::StaticId(n), AttrDefId::StaticId(t)) => {
            let n = db.type_for_static(n).skip_binder().fold_with(&mut mapper);
            let t = db.type_for_static(t).skip_binder().fold_with(&mut mapper);
            !n.has_non_region_error()
                && !t.has_non_region_error()
                && !n.has_non_region_infer()
                && n == t
        }
        (AttrDefId::ConstId(n), AttrDefId::ConstId(t)) => {
            let n = db.type_for_const(n).skip_binder().fold_with(&mut mapper);
            let t = db.type_for_const(t).skip_binder().fold_with(&mut mapper);
            !n.has_non_region_error()
                && !t.has_non_region_error()
                && !n.has_non_region_infer()
                && n == t
        }
        (AttrDefId::TypeAliasId(n), AttrDefId::TypeAliasId(t)) => {
            let n = db.ty(TyDefId::TypeAliasId(n)).skip_binder().fold_with(&mut mapper);
            let t = db.ty(TyDefId::TypeAliasId(t)).skip_binder().fold_with(&mut mapper);
            !n.has_non_region_error() && !t.has_non_region_error() && n == t
        }
        (AttrDefId::ImplId(n), AttrDefId::ImplId(t)) => {
            let n_self = db.impl_self_ty(n).skip_binder().fold_with(&mut mapper);
            let t_self = db.impl_self_ty(t).skip_binder().fold_with(&mut mapper);
            !n_self.has_non_region_error()
                && !t_self.has_non_region_error()
                && n_self == t_self
                && match (db.impl_trait(n), db.impl_trait(t)) {
                    (None, None) => true,
                    (Some(n), Some(t)) => {
                        let n = n.skip_binder();
                        let t = t.skip_binder();
                        let id = match mapper.item(t.def_id.0.into()) {
                            Some(AttrDefId::TraitId(id)) => id,
                            _ => t.def_id.0,
                        };
                        n == TraitRef::new_from_args(
                            interner,
                            id.into(),
                            t.args.fold_with(&mut mapper),
                        )
                    }
                    _ => false,
                }
        }
        _ => true,
    }
}

fn baked_type_paths(store: &ExpressionStore, expr: ExprId) -> Vec<hir_def::expr_store::path::Path> {
    struct Paths<'a> {
        store: &'a ExpressionStore,
        paths: Vec<hir_def::expr_store::path::Path>,
    }
    impl StoreVisitor for Paths<'_> {
        fn on_type(&mut self, ty: TypeRefId) {
            if let TypeRef::Path(path) = &self.store[ty] {
                self.paths.push(path.clone());
            }
            self.store.visit_type_ref_children(ty, self);
        }
    }
    let mut visitor = Paths { store, paths: Vec::new() };
    store.visit_expr_children(expr, &mut visitor);
    visitor.paths
}

fn baked_expressions(store: &ExpressionStore) -> FxHashSet<ExprId> {
    struct Roots<'a> {
        store: &'a ExpressionStore,
        expressions: FxHashSet<ExprId>,
    }
    impl StoreVisitor for Roots<'_> {
        fn on_anon_const_expr(&mut self, expr: ExprId) {
            self.expressions.insert(expr);
        }
        fn on_type(&mut self, ty: TypeRefId) {
            self.store.visit_type_ref_children(ty, self);
        }
    }
    let mut roots = Roots { store, expressions: FxHashSet::default() };
    for (expr, value) in store.exprs() {
        match value {
            Expr::Array(Array::Repeat { repeat, .. }) | Expr::Const(repeat) => {
                roots.expressions.insert(*repeat);
            }
            _ => {}
        }
        store.visit_expr_children(expr, &mut roots);
    }
    for (ty, _) in store.types.iter() {
        roots.on_type(ty);
    }
    for (pat, _) in store.pats() {
        store.walk_exprs_in_pat(pat, |expr| {
            roots.expressions.insert(expr);
        });
    }
    let mut pending: Vec<_> = roots.expressions.iter().copied().collect();
    while let Some(expr) = pending.pop() {
        store.walk_child_exprs(expr, |child| {
            if roots.expressions.insert(child) {
                pending.push(child);
            }
        });
    }
    roots.expressions
}

#[derive(Debug, PartialEq, Eq)]
struct ItemFacts {
    twin: Option<AttrDefId>,
    references: ReferenceFacts,
    reason: Option<Rejection>,
    compatible: bool,
    unknown: bool,
    impls: FxHashSet<AttrDefId>,
    impl_mismatch: bool,
}

#[salsa::interned(debug, unsafe(no_lifetime), revisions = usize::MAX)]
struct ReferenceFacts {
    #[returns(ref)]
    items: Vec<AttrDefId>,
    #[returns(ref)]
    type_items: Vec<AttrDefId>,
    #[returns(ref)]
    signature_types: Vec<AttrDefId>,
    #[returns(ref)]
    baked_items: Vec<AttrDefId>,
}

fn sorted_items(items: &FxHashSet<AttrDefId>) -> Vec<AttrDefId> {
    let mut items: Vec<_> = items.iter().copied().collect();
    items.sort_unstable_by_key(salsa::plumbing::AsId::as_id);
    items
}

#[salsa::tracked(returns(ref))]
fn eligibility_items(db: &dyn HirDatabase, krate: Crate) -> FxHashSet<AttrDefId> {
    crate_items(db, krate).items.iter().copied().collect()
}

#[salsa::tracked(returns(ref))]
fn normal_twins(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
) -> FxHashMap<AttrDefId, AttrDefId> {
    twin_index(db, normal, test).twins.iter().map(|(&t, &n)| (n, t)).collect()
}

#[salsa::tracked(returns(copy))]
fn test_only_statics(db: &dyn HirDatabase, normal: Crate, test: Crate) -> usize {
    twin_index(db, normal, test)
        .test_only
        .iter()
        .filter(|item| matches!(item, AttrDefId::StaticId(_)))
        .count()
}

#[salsa::tracked(returns(ref))]
fn eligibility_facts(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    item: AttrDefId,
) -> ItemFacts {
    let twins = twin_index(db, normal, test);
    let twin = normal_twins(db, normal, test).get(&item).copied();
    let compatible = twin.is_some_and(|t| *same_signature(db, normal, item, t));
    let per_copy = matches!(item, AttrDefId::StaticId(_)) && compatible;
    let references = references(db, item, !per_copy);
    let reason = match twin {
        Some(t) if !per_copy && twins.cfg_differing_items.contains(&t) => {
            Some(Rejection::CfgDiffering)
        }
        Some(t) if !per_copy && twins.unknown_items.contains(&t) => Some(Rejection::Unknown),
        Some(_) if references.generic_unresolved => Some(Rejection::GenericUnresolved),
        Some(_) if references.unknown => Some(Rejection::Unknown),
        Some(_) => None,
        None => Some(Rejection::Transitive),
    };
    let mut impls = FxHashSet::default();
    let mut impl_mismatch = false;
    if let AttrDefId::AdtId(adt) = item {
        let normal_impls = applicable_adt_impls(db, adt);
        impls.extend(normal_impls.iter().map(|&id| AttrDefId::ImplId(id)));
        if let Some(AttrDefId::AdtId(test)) = twin {
            let test_impls = applicable_adt_impls(db, test);
            impl_mismatch = normal_impls.len() != test_impls.len()
                || test_impls.iter().any(|&test| {
                    let Some(&AttrDefId::ImplId(normal)) = twins.twins.get(&test.into()) else {
                        return true;
                    };
                    !normal_impls.contains(&normal)
                        || !same_impl_items(db, normal, test, &twins.twins)
                });
        }
    }
    ItemFacts {
        twin,
        references: ReferenceFacts::new(
            db,
            sorted_items(&references.items),
            sorted_items(&references.type_items),
            sorted_items(&references.signature_types),
            sorted_items(&references.baked_items),
        ),
        reason,
        compatible,
        unknown: twin.is_some_and(|t| twins.unknown_items.contains(&t)),
        impls,
        impl_mismatch,
    }
}

fn local_references(db: &dyn HirDatabase, refs: ReferenceFacts) -> impl Iterator<Item = AttrDefId> {
    refs.items(db).iter().chain(refs.type_items(db)).chain(refs.signature_types(db)).copied()
}

fn local_own_reason(reason: Option<Rejection>) -> Option<LocalRejection> {
    match reason {
        Some(Rejection::CfgDiffering) => Some(LocalRejection::CfgDiffering),
        Some(Rejection::Unknown) => Some(LocalRejection::Unknown),
        _ => None,
    }
}

fn local_facts(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    item: AttrDefId,
) -> Result<ReferenceFacts, LocalRejection> {
    let twin = local_time(2, || hir_def::twins::declaration_twin(db, test, normal, item))
        .ok_or(LocalRejection::MissingTwin)?;
    let facts = hir_def::twins::local_item_twin(db, normal, test, twin);
    if facts.twin != Some(item) {
        return Err(LocalRejection::MissingTwin);
    }
    let per_copy = matches!(item, AttrDefId::StaticId(_));
    let reason = if !per_copy && facts.differs != 0 {
        Some(Rejection::CfgDiffering)
    } else if !per_copy && facts.unknown != 0 {
        Some(Rejection::Unknown)
    } else {
        None
    };
    if let Some(reason) = local_own_reason(reason) {
        return Err(reason);
    }
    if !same_signature_mode(db, normal, item, twin, true) {
        return Err(LocalRejection::Signature);
    }
    if local_impl_mismatch(db, normal, test, item) {
        return Err(LocalRejection::ImplMismatch);
    }
    let refs = references(db, item, !matches!(item, AttrDefId::StaticId(_)));
    if refs.unknown && !refs.generic_unresolved {
        return Err(LocalRejection::Unknown);
    }
    let refs = ReferenceFacts::new(
        db,
        sorted_items(&refs.items),
        sorted_items(&refs.type_items),
        sorted_items(&refs.signature_types),
        sorted_items(&refs.baked_items),
    );
    for referenced in local_references(db, refs) {
        if referenced.module(db).krate(db) != normal {
            continue;
        }
        let twin = local_time(2, || hir_def::twins::declaration_twin(db, test, normal, referenced))
            .ok_or(LocalRejection::MissingTwin)?;
        if !same_signature_mode(db, normal, referenced, twin, true) {
            return Err(LocalRejection::Signature);
        }
        if local_impl_mismatch(db, normal, test, referenced) {
            return Err(LocalRejection::ImplMismatch);
        }
    }
    Ok(refs)
}

#[salsa::tracked(returns(copy))]
fn local_impl_mismatch(db: &dyn HirDatabase, normal: Crate, test: Crate, item: AttrDefId) -> bool {
    let AttrDefId::AdtId(adt) = item else { return false };
    let Some(AttrDefId::AdtId(test_adt)) = hir_def::twins::declaration_twin(db, test, normal, item)
    else {
        return true;
    };
    let normals = applicable_adt_impls(db, adt);
    let tests = applicable_adt_impls(db, test_adt);
    normals.len() != tests.len()
        || tests.iter().any(|&test_impl| {
            let Some(AttrDefId::ImplId(normal_impl)) =
                hir_def::twins::declaration_twin(db, normal, test, test_impl.into())
            else {
                return true;
            };
            let normal_items: FxHashSet<_> = normal_impl
                .impl_items(db)
                .items
                .iter()
                .map(|(_, id)| AttrDefId::from(*id))
                .collect();
            let test_items = test_impl.impl_items(db);
            !normals.contains(&normal_impl)
                || test_items.items.len() != normal_items.len()
                || test_items.items.iter().any(|(_, id)| {
                    hir_def::twins::declaration_twin(db, normal, test, AttrDefId::from(*id))
                        .is_none_or(|id| !normal_items.contains(&id))
                })
        })
}

#[salsa::tracked(returns(copy), cycle_result = local_value_cycle)]
fn local_value_stable(db: &dyn HirDatabase, normal: Crate, test: Crate, item: AttrDefId) -> bool {
    let Ok(refs) = local_facts(db, normal, test, item) else { return false };
    local_references(db, refs).chain(refs.baked_items(db).iter().copied()).all(|referenced| {
        referenced.module(db).krate(db) != normal
            || local_value_stable(db, normal, test, referenced)
    })
}

fn local_value_cycle(
    _db: &dyn HirDatabase,
    _: salsa::Id,
    _normal: Crate,
    _test: Crate,
    _item: AttrDefId,
) -> bool {
    false
}

#[salsa::tracked(returns(copy))]
pub fn local_analysis(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    function: FunctionId,
) -> Option<LocalRejection> {
    local_time(0, || {
        if !local_time(1, || local_pair_safety(db, normal, test).is_empty()) {
            return Some(LocalRejection::PairSafety);
        }
        let source = local_time(2, || {
            hir_def::twins::local_item_twin(db, normal, test, function.into()).twin
        });
        let Some(source) = source else { return Some(LocalRejection::MissingTwin) };
        let refs = match local_facts(db, normal, test, source) {
            Ok(refs) => refs,
            Err(reason) => return Some(reason),
        };
        for &item in refs.baked_items(db) {
            if item.module(db).krate(db) == normal && !local_value_stable(db, normal, test, item) {
                return Some(LocalRejection::BakedValue);
            }
        }
        None
    })
}

#[salsa::tracked(returns(ref))]
pub fn pair_eligibility(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
    both: bool,
) -> Eligibility {
    let mut result = Eligibility {
        pair_veto: pair_safety(db, normal, test).clone(),
        test_only_statics: test_only_statics(db, normal, test),
        ..Eligibility::default()
    };
    let mut graph = DiGraph::<AttrDefId, ()>::new();
    let nodes: FxHashMap<_, _> =
        eligibility_items(db, normal).iter().map(|&item| (item, graph.add_node(item))).collect();
    let mut matched = FxHashMap::default();
    let mut compatible = FxHashSet::default();
    let mut unknown = FxHashSet::default();
    let mut own = FxHashMap::default();
    let mut all_refs = FxHashMap::default();
    let mut impl_mismatches = FxHashSet::default();
    for (&item, &node) in &nodes {
        let facts = eligibility_facts(db, normal, test, item);
        let refs = &facts.references;
        if let Some(twin) = facts.twin {
            matched.insert(item, twin);
        }
        if facts.compatible {
            compatible.insert(item);
        }
        if facts.unknown {
            unknown.insert(item);
        }
        for id in &facts.impls {
            if let Some(&dependency) = nodes.get(id) {
                graph.add_edge(node, dependency, ());
            }
        }
        if facts.impl_mismatch {
            impl_mismatches.insert(node);
        }
        if matches!(item, AttrDefId::StaticId(_)) {
            result.statics += 1;
        }
        if let Some(reason) = facts.reason {
            own.insert(node, reason);
        }
        for target in refs.items(db) {
            if let Some(&target) = nodes.get(target) {
                graph.add_edge(node, target, ());
            } else if target.module(db).krate(db) == normal {
                own.entry(node).or_insert(Rejection::Transitive);
            }
        }
        all_refs.insert(item, refs);
    }
    let rejected = reverse_closure(&graph, own.keys().copied().chain(impl_mismatches));
    let mut layout_graph = DiGraph::<AttrDefId, ()>::new();
    for &item in graph.node_weights() {
        layout_graph.add_node(item);
    }
    for (&item, refs) in &all_refs {
        let targets = if matches!(item, AttrDefId::EnumVariantId(_)) {
            refs.items(db)
        } else if matches!(item, AttrDefId::FunctionId(_)) {
            refs.signature_types(db)
        } else {
            refs.type_items(db)
        };
        for target in targets {
            if let Some(&target) = nodes.get(target) {
                layout_graph.add_edge(nodes[&item], target, ());
            }
        }
    }
    let layout_bad = reverse_closure(
        &layout_graph,
        nodes.iter().filter_map(|(&item, &node)| {
            let bad = !compatible.contains(&item)
                || match item {
                    AttrDefId::ConstId(_) => rejected.contains(&node),
                    AttrDefId::EnumVariantId(_) => {
                        own.contains_key(&node)
                            || all_refs[&item].items(db).iter().any(|target| {
                                matches!(target, AttrDefId::ConstId(_) | AttrDefId::FunctionId(_))
                                    && nodes.get(target).is_some_and(|node| rejected.contains(node))
                            })
                    }
                    AttrDefId::AdtId(_) | AttrDefId::TypeAliasId(_) => own.contains_key(&node),
                    _ => false,
                };
            bad.then_some(node)
        }),
    );
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
            .filter(|reason| *reason == Rejection::CfgDiffering || unknown.contains(&n))
            .or_else(|| {
                if let Some(reason) = own.get(&node).copied() {
                    Some(reason)
                } else if rejected.contains(&node)
                    && (all_refs[&n].items(db).iter().any(|target| {
                        target.module(db).krate(db) == normal
                            && (!compatible.contains(target)
                                || (all_refs[&n].type_items(db).contains(target)
                                    || !matches!(
                                        target,
                                        AttrDefId::ConstId(_) | AttrDefId::EnumVariantId(_)
                                    ))
                                    && nodes
                                        .get(target)
                                        .is_none_or(|node| layout_bad.contains(node)))
                    }) || all_refs[&n].baked_items(db).iter().any(|target| {
                        target.module(db).krate(db) == normal
                            && nodes.get(target).is_none_or(|node| rejected.contains(node))
                    }))
                {
                    Some(Rejection::Transitive)
                } else {
                    None
                }
            });
        if let Some(reason) = reason {
            result.rejected.insert(t, reason);
        } else if rejected.contains(&node) || static_closure.contains(&node) {
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
