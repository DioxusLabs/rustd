//! Diagnostic eligibility, without changing semantic or compilation identities.
//!
//! The reference inventory follows rustc's `MirNeighborCollector` in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_monomorphize/src/collector.rs>:
//! function operands, constants, statics, drops and unsizing can introduce code dependencies.
//! Unlike monomorphization this is a definition-level proof: unresolved dispatch,
//! opaque allocations and vtables are rejected rather than guessed.

use std::collections::VecDeque;

use base_db::{Crate, CrateOrigin, LangCrateOrigin};
use hir_def::{
    AdtId, AttrDefId, CallableDefId, DefWithBodyId, FunctionId, GenericDefId, HasModule,
    ItemContainerId, Lookup, ModuleDefId, VariantId,
    expr_store::Body,
    hir::{Expr, Pat},
    resolver::{HasResolver, ValueNs},
    signatures::{FunctionSignature, ImplSignature, StructSignature, TraitSignature},
    twins::{crate_items, scope_pairs, twin_index},
};
use hir_expand::mod_path::{ModPath, PathKind};
use petgraph::{algo::kosaraju_scc, graph::DiGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{TypeSuperVisitable, TypeVisitable, TypeVisitor, inherent::IntoKind};

use crate::{
    InferenceResult, TyDefId,
    db::{GeneralConstId, HirDatabase},
    method_resolution::CandidateId,
    mir::{Operand, OperandKind, Rvalue, StatementKind, TerminatorKind},
    next_solver::{ClauseKind, Const, ConstKind, DbInterner, GenericArgs, Ty, TyKind},
    traits::ParamEnvAndCrate,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rejection {
    CfgDiffering,
    Transitive,
    StaticClosure,
    GenericUnresolved,
    Unknown,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Eligibility {
    /// Potentially eligible T items before the crate-wide safety veto.
    pub candidates: FxHashSet<AttrDefId>,
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
    type_id_types: FxHashSet<AdtId>,
    type_id_unknown: bool,
}

#[derive(Default)]
struct TypeArguments {
    adts: FxHashSet<AdtId>,
    unknown: bool,
}

impl<'db> TypeVisitor<DbInterner<'db>> for TypeArguments {
    type Result = ();
    fn visit_ty(&mut self, ty: Ty<'db>) {
        match ty.kind() {
            TyKind::Adt(adt, _) => {
                self.adts.insert(adt.def_id());
            }
            TyKind::Param(_)
            | TyKind::Alias(..)
            | TyKind::Infer(_)
            | TyKind::Error(_)
            | TyKind::Dynamic(..)
            | TyKind::FnPtr(..) => self.unknown = true,
            _ => (),
        }
        ty.super_visit_with(self);
    }
}

struct Collector<'db> {
    db: &'db dyn HirDatabase,
    krate: Crate,
    env: ParamEnvAndCrate<'db>,
    result: References,
    seen: FxHashSet<Ty<'db>>,
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

fn body(item: AttrDefId) -> Option<DefWithBodyId> {
    match item {
        AttrDefId::FunctionId(id) => Some(id.into()),
        AttrDefId::ConstId(id) => Some(id.into()),
        AttrDefId::StaticId(id) => Some(id.into()),
        AttrDefId::EnumVariantId(id) => Some(id.into()),
        _ => None,
    }
}

fn names_type_id(db: &dyn HirDatabase, func: FunctionId) -> bool {
    if !matches!(func.krate(db).data(db).origin, CrateOrigin::Lang(LangCrateOrigin::Core)) {
        return false;
    }
    let name = FunctionSignature::of(db, func).name.as_str();
    if name == "type_id" && FunctionSignature::is_intrinsic(db, func) {
        return true;
    }
    match func.lookup(db).container {
        ItemContainerId::TraitId(id) => TraitSignature::of(db, id).name.as_str() == "Any",
        ItemContainerId::ImplId(id) => {
            if db.impl_trait(id).is_some_and(|tr| {
                TraitSignature::of(db, tr.skip_binder().def_id.0).name.as_str() == "Any"
            }) {
                return true;
            }
            matches!(db.impl_self_ty(id).skip_binder().kind(), TyKind::Adt(adt, _)
                if matches!(adt.def_id(), AdtId::StructId(id) if StructSignature::of(db, id).name.as_str() == "TypeId"))
                && name == "of"
        }
        _ => false,
    }
}

impl<'db> Collector<'db> {
    fn function(&mut self, func: FunctionId, args: GenericArgs<'db>) {
        let mut types = TypeArguments::default();
        args.visit_with(&mut types);
        if names_type_id(self.db, func) {
            self.result.type_id_types.extend(types.adts);
            self.result.type_id_unknown |= types.unknown;
            return;
        }
        if func.krate(self.db) != self.krate && types.unknown {
            self.result.generic_unresolved = true;
        }
        if func.krate(self.db) != self.krate
            && types.adts.iter().any(|adt| adt.krate(self.db) == self.krate)
        {
            self.result.unknown = true;
        }
        let (resolved, _) = self.db.lookup_impl_method(self.env, func, args);
        let either::Either::Left(resolved) = resolved else {
            self.result.unknown = true;
            return;
        };
        self.result.items.insert(resolved.into());
        match resolved.lookup(self.db).container {
            ItemContainerId::ImplId(id) => {
                self.result.items.insert(id.into());
            }
            ItemContainerId::TraitId(_) => self.result.generic_unresolved = true,
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
                if adt.def_id().krate(self.db) != self.krate {
                    let mut types = TypeArguments::default();
                    args.visit_with(&mut types);
                    self.result.unknown |=
                        types.adts.iter().any(|adt| adt.krate(self.db) == self.krate);
                }
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
            TyKind::Alias(..) => self.result.generic_unresolved = true,
            TyKind::Dynamic(..)
            | TyKind::FnPtr(..)
            | TyKind::Closure(..)
            | TyKind::Coroutine(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::CoroutineWitness(..)
            | TyKind::Error(..)
            | TyKind::Infer(..) => self.result.unknown = true,
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
fn references(db: &dyn HirDatabase, item: AttrDefId) -> References {
    let krate = item.module(db).krate(db);
    let env = ParamEnvAndCrate {
        param_env: generic(item)
            .map_or_else(crate::next_solver::ParamEnv::empty, |id| db.trait_environment(id)),
        krate,
    };
    let mut c =
        Collector { db, krate, env, result: References::default(), seen: FxHashSet::default() };
    env.param_env.visit_with(&mut c);
    if let Some(def) = generic(item) {
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
            db.ty(TyDefId::TypeAliasId(id)).skip_binder().visit_with(&mut c);
        }
        AttrDefId::ImplId(id) => {
            db.impl_self_ty(id).skip_binder().visit_with(&mut c);
            if let Some(tr) = db.impl_trait(id) {
                c.result.items.insert(tr.skip_binder().def_id.0.into());
                tr.skip_binder().visit_with(&mut c);
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
    if let Some(owner) = body(item) {
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
        match db.mir_body(owner.into()) {
            Err(_) => c.result.unknown = true,
            Ok(mir) => {
                c.result.unknown |= !mir.closures.is_empty();
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
                            c.result.generic_unresolved |=
                                !crate::collect_params(&mir.locals[place.local].ty.as_ref())
                                    .is_empty();
                        }
                        match &term.kind {
                            TerminatorKind::Call { func, args, .. } => {
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

#[salsa::tracked(returns(ref))]
pub fn pair_safety(db: &dyn HirDatabase, normal: Crate, test: Crate) -> Vec<&'static str> {
    let mut veto = FxHashSet::default();
    let twins = twin_index(db, normal, test);
    let nitems = crate_items(db, normal);
    let titems = crate_items(db, test);
    for (&def, &item) in &titems.definitions {
        if matches!(def.kind, hir_expand::MacroDefKind::Declarative(..))
            && !nitems.definitions.values().any(|&n| twins.twins.get(&item) == Some(&n))
        {
            let reads = hir_def::twins::item_cfg_reads(db, item);
            if reads.differs_from(normal.cfg_options(db)) {
                veto.insert("cfg-test-macro-rules");
            }
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
    let mut own = FxHashMap::default();
    for (&item, &node) in &nodes {
        let refs = references(db, item);
        let reason = if let Some(&t) = matched.get(&item) {
            if twins.cfg_differing_items.contains(&t) {
                Some(Rejection::CfgDiffering)
            } else if both && matches!(item, AttrDefId::StaticId(_)) {
                Some(Rejection::StaticClosure)
            } else if twins.unknown_items.contains(&t) {
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
                if static_closure.contains(&node) {
                    Some(Rejection::StaticClosure)
                } else if let Some(reason) = own.get(&node).copied() {
                    Some(reason)
                } else if rejected.contains(&node) {
                    Some(Rejection::Transitive)
                } else {
                    None
                }
            });
        if let Some(reason) = reason {
            result.rejected.insert(t, reason);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeIdVeto {
    None,
    TypeId,
    Unknown(AttrDefId),
}

pub fn type_id_preflight(
    db: &dyn HirDatabase,
    roots: &[AttrDefId],
    normal: Crate,
    test: Crate,
) -> TypeIdVeto {
    let eligible = pair_eligibility(db, normal, test, true);
    if eligible.candidates.is_empty() {
        return TypeIdVeto::None;
    }
    let mut seen = FxHashSet::default();
    let mut pending: VecDeque<_> = roots.iter().copied().collect();
    let mut roots_left = pending.len();
    let mut unknown = None;
    while let Some(item) = pending.pop_front() {
        roots_left = roots_left.saturating_sub(1);
        if !seen.insert(item) {
            continue;
        }
        let refs = references(db, item);
        let twins = twin_index(db, normal, test);
        if refs.type_id_types.iter().any(|&adt| {
            let item = adt.into();
            eligible.candidates.contains(&item)
                || twins.twins.iter().any(|(t, n)| *n == item && eligible.candidates.contains(t))
        }) {
            return TypeIdVeto::TypeId;
        }
        if refs.unknown || refs.generic_unresolved || refs.type_id_unknown {
            unknown.get_or_insert(item);
        }
        if roots_left == 0
            && let Some(item) = unknown
        {
            return TypeIdVeto::Unknown(item);
        }
        pending.extend(refs.items.iter().copied());
    }
    unknown.map_or(TypeIdVeto::None, TypeIdVeto::Unknown)
}
