use base_db::Crate;
use hir_def::{AttrDefId, CallableDefId, DefWithBodyId, FunctionId, HasModule};
use rustc_type_ir::{
    TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor,
    inherent::{IntoKind, Ty as _},
};

use crate::{
    InferBodyId,
    db::{HirDatabase, InternedClosureId, InternedCoroutineId},
    next_solver::{DbInterner, Ty, TyKind},
    traits::{ParamEnvAndCrate, StoredParamEnvAndCrate},
};

use super::{Instance, InstanceDef};

/// The crate copies present in one program. An empty policy compiles without sharing.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Sharing {
    pairs: Vec<(Crate, Crate, bool)>,
    enabled: bool,
}

impl Sharing {
    pub fn new(pairs: Vec<(Crate, Crate, bool)>) -> Self {
        Self { pairs, enabled: true }
    }

    pub fn disabled(mut self) -> Self {
        self.enabled = false;
        self
    }

    pub(super) fn is_empty(&self) -> bool {
        !self.enabled || self.pairs.is_empty()
    }

    pub(super) fn tentative(&self) -> bool {
        self.enabled && self.pairs.iter().any(|it| it.2)
    }

    pub(super) fn test_crate(&self, krate: Crate) -> bool {
        self.pairs.iter().any(|it| it.1 == krate)
    }

    pub(super) fn edited_crates(&self, edited: &mut rustc_hash::FxHashSet<Crate>) {
        if self.is_empty() {
            return;
        }
        for &(normal, test, _) in &self.pairs {
            if edited.contains(&test) {
                edited.insert(normal);
            }
        }
    }

    pub(super) fn item(&self, db: &dyn HirDatabase, item: AttrDefId) -> AttrDefId {
        if self.is_empty() {
            return item;
        }
        for &(normal, test, both) in &self.pairs {
            if item.module(db).krate(db) != test {
                continue;
            }
            let eligibility = crate::sharing::pair_eligibility(db, normal, test, both);
            if eligibility.pair_veto.is_empty() && eligibility.candidates.contains(&item) {
                return hir_def::twins::twin_index(db, normal, test)
                    .twins
                    .get(&item)
                    .copied()
                    .unwrap_or(item);
            }
        }
        item
    }

    pub(super) fn analysis_shared(&self, db: &dyn HirDatabase, func: FunctionId) -> bool {
        self.pairs.iter().any(|&(n, t, both)| {
            func.krate(db) == t
                && crate::sharing::pair_eligibility(db, n, t, both)
                    .analysis_shared
                    .contains(&func.into())
        })
    }

    pub(super) fn function(&self, db: &dyn HirDatabase, func: FunctionId) -> FunctionId {
        match self.item(db, func.into()) {
            AttrDefId::FunctionId(it) => it,
            _ => func,
        }
    }

    fn owner<'db>(&self, db: &'db dyn HirDatabase, owner: InferBodyId<'db>) -> InferBodyId<'db> {
        match owner {
            InferBodyId::DefWithBodyId(DefWithBodyId::FunctionId(f)) => self.function(db, f).into(),
            _ => owner,
        }
    }

    fn def(&self, db: &dyn HirDatabase, def: InstanceDef) -> InstanceDef {
        use salsa::plumbing::{AsId, FromId};
        match def {
            InstanceDef::Fn(f) => InstanceDef::Fn(self.function(db, f)),
            InstanceDef::VtableShim(f) => InstanceDef::VtableShim(self.function(db, f)),
            InstanceDef::Closure(id) => {
                let mut loc = InternedClosureId::from_id(id).loc(db);
                loc.owner = self.owner(db, loc.owner);
                InstanceDef::Closure(InternedClosureId::new(db, loc).as_id())
            }
            InstanceDef::Coroutine(id) | InstanceDef::CoroutineByMove(id) => {
                let mut loc = InternedCoroutineId::from_id(id).loc(db);
                loc.owner = self.owner(db, loc.owner);
                let id = InternedCoroutineId::new(db, loc).as_id();
                if matches!(def, InstanceDef::Coroutine(_)) {
                    InstanceDef::Coroutine(id)
                } else {
                    InstanceDef::CoroutineByMove(id)
                }
            }
            _ => def,
        }
    }

    pub(super) fn fold<'db, T: TypeFoldable<DbInterner<'db>>>(
        &self,
        db: &'db dyn HirDatabase,
        krate: Crate,
        value: T,
    ) -> T {
        if self.is_empty() {
            return value;
        }
        value.fold_with(&mut Canonical {
            db,
            sharing: self,
            interner: DbInterner::new_with(db, krate),
            reverse: false,
        })
    }

    pub(super) fn link_type<'db>(&self, db: &'db dyn HirDatabase, ty: Ty<'db>) -> Ty<'db> {
        if self.is_empty() {
            return ty;
        }
        ty.fold_with(&mut Canonical {
            db,
            sharing: self,
            interner: DbInterner::new_no_crate(db),
            reverse: true,
        })
    }

    fn link_item(&self, db: &dyn HirDatabase, item: AttrDefId) -> AttrDefId {
        for &(normal, test, both) in &self.pairs {
            if !both && item.module(db).krate(db) == normal {
                if let Some((&t, _)) = hir_def::twins::twin_index(db, normal, test)
                    .twins
                    .iter()
                    .find(|(_, n)| **n == item)
                {
                    return t;
                }
            }
        }
        item
    }

    pub(super) fn instance(&self, db: &dyn HirDatabase, instance: &Instance) -> Instance {
        if self.is_empty() {
            return instance.clone();
        }
        let Some(krate) = self.pairs.first().map(|it| it.0) else { return instance.clone() };
        let args = self.fold(db, krate, instance.args.as_ref());
        // A test-only argument can select an impl absent from N's trait namespace.
        // Keep that instance's semantic identity in T until instance-level eligibility proves it.
        let mut remaining = TestTypes { db, sharing: self, found: false };
        args.visit_with(&mut remaining);
        let def = if remaining.found { instance.def } else { self.def(db, instance.def) };
        let canonical = Instance {
            def,
            args: if remaining.found { instance.args.clone() } else { args.store() },
            checked: instance.checked,
        };
        if self.test_body(db, &canonical) { instance.clone() } else { canonical }
    }

    pub(super) fn env(
        &self,
        db: &dyn HirDatabase,
        instance: &Instance,
        env: &StoredParamEnvAndCrate,
    ) -> StoredParamEnvAndCrate {
        if self.is_empty() || self.needs_policy(db, instance) {
            return env.clone();
        }
        let env = env.as_ref(db);
        let krate = self.pairs.iter().find(|it| it.1 == env.krate).map_or(env.krate, |it| it.0);
        ParamEnvAndCrate { krate, param_env: self.fold(db, krate, env.param_env) }.store()
    }

    pub(super) fn needs_policy(&self, db: &dyn HirDatabase, instance: &Instance) -> bool {
        let mut types = TestTypes { db, sharing: self, found: false };
        instance.args.as_ref().visit_with(&mut types);
        types.found || self.test_body(db, instance)
    }

    pub(super) fn type_env<'db>(
        &self,
        db: &'db dyn HirDatabase,
        ty: Ty<'db>,
        env: ParamEnvAndCrate<'db>,
    ) -> ParamEnvAndCrate<'db> {
        if self.is_empty() {
            return env;
        }
        let mut remaining = TestTypes { db, sharing: self, found: false };
        ty.visit_with(&mut remaining);
        if remaining.found {
            return env;
        }
        let krate = self.pairs.iter().find(|it| it.1 == env.krate).map_or(env.krate, |it| it.0);
        ParamEnvAndCrate { krate, param_env: self.fold(db, krate, env.param_env) }
    }

    fn test_body(&self, db: &dyn HirDatabase, instance: &Instance) -> bool {
        let owner = match instance.def {
            InstanceDef::VtableShim(func) => Some(func),
            _ => super::home::written_in(db, instance),
        };
        owner.is_some_and(|f| self.test_crate(f.krate(db)))
    }

    pub(super) fn link_instance(&self, db: &dyn HirDatabase, instance: &Instance) -> Instance {
        let mut instance = instance.clone();
        if let InstanceDef::Fn(func) = instance.def {
            instance.def = InstanceDef::Fn(self.link_function(db, func));
        }
        instance
    }

    pub(super) fn link_static(
        &self,
        db: &dyn HirDatabase,
        id: hir_def::StaticId,
    ) -> hir_def::StaticId {
        if self.is_empty() {
            return id;
        }
        for &(normal, test, both) in &self.pairs {
            if !both && id.krate(db) == normal {
                if let Some((&AttrDefId::StaticId(t), _)) =
                    hir_def::twins::twin_index(db, normal, test)
                        .twins
                        .iter()
                        .find(|(_, n)| **n == id.into())
                {
                    return t;
                }
            }
        }
        id
    }

    pub(super) fn contains_unified(&self, db: &dyn HirDatabase, ty: Ty<'_>) -> bool {
        if !self.tentative() {
            return false;
        }
        let mut visitor = Unified { db, sharing: self, found: false };
        ty.visit_with(&mut visitor);
        visitor.found
    }

    pub(super) fn link_function(&self, db: &dyn HirDatabase, func: FunctionId) -> FunctionId {
        if self.is_empty() {
            return func;
        }
        for &(normal, test, both) in &self.pairs {
            if !both && func.krate(db) == normal {
                let twins = hir_def::twins::twin_index(db, normal, test);
                if let Some((&AttrDefId::FunctionId(t), _)) =
                    twins.twins.iter().find(|(_, n)| **n == func.into())
                {
                    return t;
                }
            }
        }
        func
    }
}

struct Canonical<'a, 'db> {
    db: &'db dyn HirDatabase,
    sharing: &'a Sharing,
    interner: DbInterner<'db>,
    reverse: bool,
}

impl<'db> Canonical<'_, 'db> {
    fn item(&self, item: AttrDefId) -> AttrDefId {
        if self.reverse {
            self.sharing.link_item(self.db, item)
        } else {
            self.sharing.item(self.db, item)
        }
    }

    fn function(&self, id: FunctionId) -> FunctionId {
        match self.item(id.into()) {
            AttrDefId::FunctionId(id) => id,
            _ => id,
        }
    }

    fn owner(&self, id: InferBodyId<'db>) -> InferBodyId<'db> {
        match id {
            InferBodyId::DefWithBodyId(DefWithBodyId::FunctionId(f)) => self.function(f).into(),
            _ => id,
        }
    }

    fn solver_def(
        &self,
        id: crate::next_solver::SolverDefId<'db>,
    ) -> crate::next_solver::SolverDefId<'db> {
        use crate::{ImplTraitId, db::InternedOpaqueTyId, next_solver::SolverDefId};
        match id {
            SolverDefId::ConstId(id) => match self.item(id.into()) {
                AttrDefId::ConstId(id) => id.into(),
                _ => id.into(),
            },
            SolverDefId::TypeAliasId(id) => match self.item(id.into()) {
                AttrDefId::TypeAliasId(id) => id.into(),
                _ => id.into(),
            },
            SolverDefId::InternedOpaqueTyId(id) => {
                let loc = match id.loc(self.db) {
                    ImplTraitId::ReturnTypeImplTrait(func, index) => {
                        ImplTraitId::ReturnTypeImplTrait(self.function(func), index)
                    }
                    ImplTraitId::TypeAliasImplTrait(alias, index) => {
                        match self.item(alias.into()) {
                            AttrDefId::TypeAliasId(alias) => {
                                ImplTraitId::TypeAliasImplTrait(alias, index)
                            }
                            _ => id.loc(self.db),
                        }
                    }
                };
                InternedOpaqueTyId::new(self.db, loc).into()
            }
            _ => id,
        }
    }
}

impl<'db> TypeFolder<DbInterner<'db>> for Canonical<'_, 'db> {
    fn cx(&self) -> DbInterner<'db> {
        self.interner
    }

    fn fold_const(
        &mut self,
        value: crate::next_solver::Const<'db>,
    ) -> crate::next_solver::Const<'db> {
        use crate::{
            db::GeneralConstId,
            next_solver::{Const, ConstKind},
        };
        let value = value.super_fold_with(self);
        if let ConstKind::Unevaluated(mut unevaluated) = value.kind()
            && let GeneralConstId::ConstId(id) = unevaluated.def.0
            && let AttrDefId::ConstId(id) = self.item(id.into())
        {
            unevaluated.def = GeneralConstId::ConstId(id).into();
            return Const::new(self.interner, ConstKind::Unevaluated(unevaluated));
        }
        value
    }

    fn fold_predicate(
        &mut self,
        value: crate::next_solver::Predicate<'db>,
    ) -> crate::next_solver::Predicate<'db> {
        use crate::next_solver::{ClauseKind, Predicate, PredicateKind};
        let value = value.super_fold_with(self).kind().map_bound(|mut kind| {
            if let PredicateKind::Clause(ClauseKind::Trait(tr)) = &mut kind
                && let AttrDefId::TraitId(id) = self.item(tr.trait_ref.def_id.0.into())
            {
                tr.trait_ref.def_id = id.into();
            }
            if let PredicateKind::Clause(ClauseKind::Projection(projection)) = &mut kind {
                let term = projection.projection_term;
                projection.projection_term = rustc_type_ir::AliasTerm::new_from_def_id(
                    self.interner,
                    self.solver_def(term.def_id()),
                    term.args,
                );
            }
            kind
        });
        Predicate::new(self.interner, value)
    }

    fn fold_ty(&mut self, ty: Ty<'db>) -> Ty<'db> {
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                if let AttrDefId::AdtId(id) = self.item(adt.def_id().into()) {
                    return Ty::new_adt(self.interner, id, args.fold_with(self));
                }
            }
            TyKind::FnDef(def, args) => {
                let def = match def.0 {
                    CallableDefId::FunctionId(f) => self.function(f).into(),
                    CallableDefId::StructId(s) => {
                        match self.item(hir_def::AdtId::StructId(s).into()) {
                            AttrDefId::AdtId(hir_def::AdtId::StructId(s)) => s.into(),
                            _ => def.0,
                        }
                    }
                    CallableDefId::EnumVariantId(v) => match self.item(v.into()) {
                        AttrDefId::EnumVariantId(v) => v.into(),
                        _ => def.0,
                    },
                };
                return Ty::new_fn_def(self.interner, def.into(), args.fold_with(self));
            }
            TyKind::Closure(id, args) => {
                let mut loc = id.0.loc(self.db);
                loc.owner = self.owner(loc.owner);
                return Ty::new_closure(
                    self.interner,
                    InternedClosureId::new(self.db, loc).into(),
                    args.fold_with(self),
                );
            }
            TyKind::Coroutine(id, args) => {
                let mut loc = id.0.loc(self.db);
                loc.owner = self.owner(loc.owner);
                return Ty::new_coroutine(
                    self.interner,
                    InternedCoroutineId::new(self.db, loc).into(),
                    args.fold_with(self),
                );
            }
            TyKind::Dynamic(bounds, region) => {
                use crate::next_solver::{BoundExistentialPredicates, ExistentialPredicate};
                let interner = self.interner;
                let predicates = bounds.iter().map(|bound| {
                    bound.map_bound(|pred| {
                        let mut pred = pred.fold_with(self);
                        match &mut pred {
                            ExistentialPredicate::Trait(tr) => {
                                if let AttrDefId::TraitId(id) = self.item(tr.def_id.0.into()) {
                                    tr.def_id = id.into();
                                }
                            }
                            ExistentialPredicate::AutoTrait(id) => {
                                if let AttrDefId::TraitId(mapped) = self.item(id.0.into()) {
                                    *id = mapped.into();
                                }
                            }
                            ExistentialPredicate::Projection(projection) => {
                                projection.def_id = self
                                    .solver_def(projection.def_id.into())
                                    .try_into()
                                    .unwrap_or(projection.def_id);
                            }
                        }
                        pred
                    })
                });
                return Ty::new_dynamic(
                    interner,
                    BoundExistentialPredicates::new_from_iter(predicates),
                    region,
                );
            }
            TyKind::Alias(mut alias) => {
                alias.kind = rustc_type_ir::AliasTyKind::new_from_def_id(
                    self.interner,
                    self.solver_def(alias.kind.def_id()),
                );
                alias.args = alias.args.fold_with(self);
                return Ty::new(self.interner, TyKind::Alias(alias));
            }
            _ => {}
        }
        ty.super_fold_with(self)
    }
}

struct TestTypes<'a, 'db> {
    db: &'db dyn HirDatabase,
    sharing: &'a Sharing,
    found: bool,
}
impl<'db> TypeVisitor<DbInterner<'db>> for TestTypes<'_, 'db> {
    type Result = ();
    fn visit_ty(&mut self, ty: Ty<'db>) {
        if let Some(item) = type_item(self.db, ty) {
            self.found |= self.sharing.test_crate(item.module(self.db).krate(self.db));
        }
        ty.super_visit_with(self);
    }
}

struct Unified<'a, 'db> {
    db: &'db dyn HirDatabase,
    sharing: &'a Sharing,
    found: bool,
}
impl<'db> TypeVisitor<DbInterner<'db>> for Unified<'_, 'db> {
    type Result = ();
    fn visit_ty(&mut self, ty: Ty<'db>) {
        if let Some(item) = type_item(self.db, ty) {
            for &(normal, test, both) in &self.sharing.pairs {
                if !both {
                    continue;
                }
                let twins = hir_def::twins::twin_index(self.db, normal, test);
                self.found |= twins
                    .twins
                    .iter()
                    .any(|(&t, &n)| (item == t || item == n) && self.sharing.item(self.db, t) == n);
            }
        }
        ty.super_visit_with(self);
    }
}

fn type_item(db: &dyn HirDatabase, ty: Ty<'_>) -> Option<AttrDefId> {
    let owner = match ty.kind() {
        TyKind::Adt(adt, _) => return Some(adt.def_id().into()),
        TyKind::FnDef(def, _) => {
            return Some(match def.0 {
                CallableDefId::FunctionId(id) => id.into(),
                CallableDefId::StructId(id) => hir_def::AdtId::StructId(id).into(),
                CallableDefId::EnumVariantId(id) => id.into(),
            });
        }
        TyKind::Dynamic(bounds, _) => {
            use rustc_type_ir::inherent::BoundExistentialPredicates as _;
            return bounds.principal_def_id().map(|id| id.0.into());
        }
        TyKind::Alias(alias) => match alias.kind.def_id() {
            crate::next_solver::SolverDefId::TypeAliasId(id) => return Some(id.into()),
            crate::next_solver::SolverDefId::InternedOpaqueTyId(id) => {
                return Some(match id.loc(db) {
                    crate::ImplTraitId::ReturnTypeImplTrait(id, _) => id.into(),
                    crate::ImplTraitId::TypeAliasImplTrait(id, _) => id.into(),
                });
            }
            _ => return None,
        },
        TyKind::Closure(id, _) => id.0.loc(db).owner,
        TyKind::Coroutine(id, _) => id.0.loc(db).owner,
        _ => return None,
    };
    match owner {
        InferBodyId::DefWithBodyId(DefWithBodyId::FunctionId(id)) => Some(id.into()),
        _ => None,
    }
}
