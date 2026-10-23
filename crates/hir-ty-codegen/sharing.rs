use base_db::Crate;
use hir_def::{AttrDefId, CallableDefId, DefWithBodyId, FunctionId, HasModule, Lookup};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{
    TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor,
    inherent::{IntoKind, Ty as _},
};
use std::{
    hash::{Hash, Hasher},
    sync::Arc,
    time::Instant,
};

use crate::{
    InferBodyId,
    db::{HirDatabase, InternedClosureId, InternedCoroutineClosureId, InternedCoroutineId},
    next_solver::{DbInterner, Ty, TyKind},
    traits::{ParamEnvAndCrate, StoredParamEnvAndCrate},
};

use super::{Instance, InstanceDef};

#[salsa::tracked(returns(ref))]
fn reverse_twins(
    db: &dyn HirDatabase,
    normal: Crate,
    test: Crate,
) -> rustc_hash::FxHashMap<AttrDefId, AttrDefId> {
    hir_def::twins::twin_index(db, normal, test).twins.iter().map(|(&t, &n)| (n, t)).collect()
}

#[salsa::tracked(returns(copy))]
fn decision_serial(db: &dyn HirDatabase, normal: Crate, test: Crate, both: bool) -> u128 {
    let twins = reverse_twins(db, normal, test);
    let eligibility = crate::sharing::pair_eligibility(db, normal, test, both);
    policy_serial(twins, eligibility)
}

fn policy_serial(
    twins: &FxHashMap<AttrDefId, AttrDefId>,
    eligibility: &crate::sharing::Eligibility,
) -> u128 {
    let mut twins: Vec<_> = twins.iter().map(|(&n, &t)| super::print_of(&(&t, &n))).collect();
    let mut full: Vec<_> = eligibility.candidates.iter().map(super::print_of).collect();
    let mut analysis: Vec<_> = eligibility.analysis_shared.iter().map(super::print_of).collect();
    twins.sort_unstable();
    full.sort_unstable();
    analysis.sort_unstable();
    super::print_of(&(twins, full, analysis, &eligibility.pair_veto))
}

/// The crate copies present in one program. An empty policy compiles without sharing.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Sharing {
    pairs: Vec<(Crate, Crate, bool)>,
    enabled: bool,
    snapshot: Option<Arc<Policy>>,
}

#[derive(Debug, Clone)]
struct PairPolicy {
    key: (Crate, Crate, bool, u128),
    twins: hir_def::twins::TwinIndex,
    reverse: FxHashMap<AttrDefId, AttrDefId>,
    eligibility: crate::sharing::Eligibility,
}

#[derive(Debug, Clone)]
struct Policy(Vec<PairPolicy>);

impl PartialEq for Policy {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().map(|it| it.key).eq(other.0.iter().map(|it| it.key))
    }
}
impl Eq for Policy {}
impl Hash for Policy {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
        for pair in &self.0 {
            pair.key.hash(state);
        }
    }
}

#[derive(Default, Clone)]
pub(super) struct Cache {
    input: Option<Sharing>,
    shared: Option<Sharing>,
    files: FxHashMap<base_db::FileId, FileFacts>,
    changed: FxHashSet<base_db::FileId>,
    eligibility: Vec<((Crate, Crate, bool), crate::sharing::EligibilityState)>,
}

#[derive(Default, Clone)]
struct FileFacts {
    trees: Vec<(Crate, hir_expand::HirFileId, Option<Arc<hir_def::item_tree::ItemTree>>)>,
    bodies: Vec<(FunctionId, bool, crate::sharing::BodySharingFacts)>,
}

impl Cache {
    pub(super) fn clear(&mut self) {
        *self = Self::default();
    }

    pub(super) fn touch(&mut self, file: base_db::FileId) {
        self.changed.insert(file);
    }

    pub(super) fn needs_before_edit(&self, files: &[base_db::FileId]) -> bool {
        self.shared.as_ref().is_some_and(|sharing| !sharing.is_empty())
            && files.iter().any(|file| !self.files.contains_key(file))
    }

    pub(super) fn before_edit(
        &mut self,
        db: &dyn HirDatabase,
        file: base_db::FileId,
        functions: &[FunctionId],
    ) {
        if self.shared.as_ref().is_none_or(Sharing::is_empty)
            || self.files.contains_key(&file)
            || functions.is_empty()
        {
            return;
        }
        let mut facts = FileFacts::default();
        for &func in functions {
            let source = func.lookup(db).id.file_id;
            let krate = func.krate(db);
            if func.module(db).block(db).is_none()
                && !facts.trees.iter().any(|&(k, f, _)| k == krate && f == source)
            {
                facts.trees.push((
                    krate,
                    source,
                    hir_def::item_tree::file_item_tree_snapshot(db, source, krate),
                ));
            }
            if hir_def::signatures::FunctionSignature::of(db, func).has_body() {
                facts.bodies.push((
                    func,
                    true,
                    crate::sharing::body_sharing_facts(db, func, true).clone(),
                ));
            }
        }
        self.files.insert(file, facts);
    }

    pub(super) fn sharing(
        &mut self,
        db: &dyn HirDatabase,
        input: Sharing,
        program: &str,
    ) -> Sharing {
        let start = Instant::now();
        let changed = std::mem::take(&mut self.changed);
        let mut reason = "policy input changed";
        let mut updates = Vec::new();
        let mut bodies = FxHashSet::default();
        let stable = self.input.as_ref() == Some(&input)
            && changed.iter().all(|file| {
                let Some(facts) = self.files.get(file) else {
                    reason = "changed file has no retained facts";
                    return false;
                };
                facts.trees.iter().all(|(krate, file, tree)| {
                    reason = "item tree changed";
                    &hir_def::item_tree::file_item_tree_snapshot(db, *file, *krate) == tree
                }) && facts.bodies.iter().enumerate().all(|(index, (func, normal, facts))| {
                    reason = "body facts changed";
                    let new = crate::sharing::body_sharing_facts(db, *func, *normal);
                    if new == facts {
                        return true;
                    }
                    if std::env::var_os("RUSTD_STATS").is_some() {
                        for (field, old, new) in facts.changed_fields(new) {
                            eprintln!(
                                "sharing fact mismatch: owner={func:?} name={} normal={normal} field={field} old={old} new={new}; program={program}",
                                hir_def::signatures::FunctionSignature::of(db, *func).name.as_str(),
                            );
                        }
                    }
                    if !facts.same_structure(new) {
                        return false;
                    }
                    let krate = func.krate(db);
                    let crates: Vec<_> = input
                        .pairs
                        .iter()
                        .filter(|&&(normal, _, _)| normal == krate)
                        .flat_map(|&(normal, test, _)| [normal, test])
                        .collect();
                    if facts.policy_projection(db, &crates) != new.policy_projection(db, &crates) {
                        bodies.insert(*func);
                    }
                    updates.push((*file, index, new.clone()));
                    true
                })
            });
        let validated = start.elapsed();
        let rejected_before: usize = self
            .shared
            .as_ref()
            .into_iter()
            .flat_map(|it| it.snapshot.iter())
            .flat_map(|it| &it.0)
            .map(|it| it.eligibility.rejected.len())
            .sum();
        let retained = if stable { self.shared.clone() } else { None };
        let mut affected = 0;
        let retained = retained.and_then(|mut shared| {
            if bodies.is_empty() {
                return Some(shared);
            }
            let mut policy = shared.snapshot.as_deref()?.clone();
            let mut handled = FxHashSet::default();
            for ((normal, test, both), state) in &mut self.eligibility {
                let changed: Vec<_> =
                    bodies.iter().copied().filter(|func| func.krate(db) == *normal).collect();
                if changed.is_empty() {
                    continue;
                }
                affected += state.update(db, *normal, *test, *both, &changed)?;
                handled.extend(changed);
                let pair = policy
                    .0
                    .iter_mut()
                    .find(|pair| (pair.key.0, pair.key.1, pair.key.2) == (*normal, *test, *both))?;
                if &pair.eligibility != state.result() {
                    pair.eligibility = state.result().clone();
                    pair.key.3 = policy_serial(&pair.reverse, &pair.eligibility);
                }
            }
            if handled != bodies {
                reason = "changed body is outside retained eligibility graph";
                return None;
            }
            shared.snapshot = Some(Arc::new(policy));
            Some(shared)
        });
        if let Some(shared) = retained {
            if std::env::var_os("RUSTD_VERIFY_FASTPATH").is_some_and(|it| it == "1") {
                let full = input.clone().capture(db);
                for (cached, full) in shared
                    .snapshot
                    .iter()
                    .flat_map(|it| &it.0)
                    .zip(full.snapshot.iter().flat_map(|it| &it.0))
                {
                    assert_eq!(cached.twins, full.twins, "sharing twins fast path");
                    assert_eq!(
                        cached.eligibility, full.eligibility,
                        "sharing eligibility fast path"
                    );
                }
                assert_eq!(
                    shared.decisions(db),
                    full.decisions(db),
                    "sharing fingerprint fast path"
                );
            }
            if !input.is_empty() && std::env::var_os("RUSTD_STATS").is_some() {
                if bodies.is_empty() {
                    eprintln!("sharing fast path: unchanged facts; program={program}");
                } else {
                    let rejected: usize = shared
                        .snapshot
                        .iter()
                        .flat_map(|it| &it.0)
                        .map(|it| it.eligibility.rejected.len())
                        .sum();
                    eprintln!(
                        "sharing incremental path: bodies={} affected={affected} rejected={rejected_before}->{rejected}; program={program}",
                        bodies.len()
                    );
                }
                eprintln!("sharing validate-us: {}; program={program}", validated.as_micros());
            }
            for (file, index, facts) in updates {
                self.files.get_mut(&file).unwrap().bodies[index].2 = facts;
            }
            self.shared = Some(shared.clone());
            return shared;
        }
        if !input.is_empty() && std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!("sharing full path: {reason}; program={program}");
        }
        let shared = input.clone().capture(db);
        let captured = start.elapsed();
        self.eligibility = input
            .pairs
            .iter()
            .map(|&(normal, test, both)| {
                let state = crate::sharing::EligibilityState::new(db, normal, test, both);
                assert_eq!(
                    state.result(),
                    crate::sharing::pair_eligibility(db, normal, test, both),
                    "sharing retained evaluator initialization"
                );
                ((normal, test, both), state)
            })
            .collect();
        self.files.clear();
        if !input.is_empty() {
            let mut crates = FxHashMap::default();
            for &(normal, test, _) in &input.pairs {
                crates.insert(normal, true);
                crates.entry(test).or_insert(false);
            }
            for (krate, normal) in crates {
                for &item in &hir_def::twins::crate_items(db, krate).items {
                    let AttrDefId::FunctionId(func) = item else { continue };
                    if !hir_def::signatures::FunctionSignature::of(db, func).has_body() {
                        continue;
                    }
                    let source = func.lookup(db).id.file_id;
                    let file = super::home::body_file(db, func.into());
                    let facts = self.files.entry(file).or_default();
                    if func.module(db).block(db).is_none()
                        && !facts.trees.iter().any(|&(k, f, _)| k == krate && f == source)
                    {
                        facts.trees.push((
                            krate,
                            source,
                            hir_def::item_tree::file_item_tree_snapshot(db, source, krate),
                        ));
                    }
                    facts.bodies.push((
                        func,
                        normal,
                        crate::sharing::body_sharing_facts(db, func, normal).clone(),
                    ));
                }
            }
        }
        self.input = Some(input);
        self.shared = Some(shared.clone());
        if !shared.is_empty() && std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!(
                "sharing phases-us: validate={} capture={} inventory={}; program={program}",
                validated.as_micros(),
                (captured - validated).as_micros(),
                (start.elapsed() - captured).as_micros(),
            );
        }
        shared
    }
}

impl Sharing {
    fn capture(mut self, db: &dyn HirDatabase) -> Self {
        if !self.is_empty() {
            self.snapshot = Some(Arc::new(Policy(
                self.pairs
                    .iter()
                    .map(|&(n, t, both)| PairPolicy {
                        key: (n, t, both, decision_serial(db, n, t, both)),
                        twins: hir_def::twins::twin_index(db, n, t).clone(),
                        reverse: reverse_twins(db, n, t).clone(),
                        eligibility: crate::sharing::pair_eligibility(db, n, t, both).clone(),
                    })
                    .collect(),
            )));
        }
        self
    }

    fn policy(&self, normal: Crate, test: Crate) -> Option<&PairPolicy> {
        self.snapshot.as_ref()?.0.iter().find(|it| (it.key.0, it.key.1) == (normal, test))
    }

    fn twins<'a>(
        &'a self,
        db: &'a dyn HirDatabase,
        normal: Crate,
        test: Crate,
    ) -> &'a hir_def::twins::TwinIndex {
        self.policy(normal, test)
            .map(|it| &it.twins)
            .unwrap_or_else(|| hir_def::twins::twin_index(db, normal, test))
    }

    fn reverse<'a>(
        &'a self,
        db: &'a dyn HirDatabase,
        normal: Crate,
        test: Crate,
    ) -> &'a FxHashMap<AttrDefId, AttrDefId> {
        self.policy(normal, test)
            .map(|it| &it.reverse)
            .unwrap_or_else(|| reverse_twins(db, normal, test))
    }

    fn eligibility<'a>(
        &'a self,
        db: &'a dyn HirDatabase,
        normal: Crate,
        test: Crate,
        both: bool,
    ) -> &'a crate::sharing::Eligibility {
        self.policy(normal, test)
            .map(|it| &it.eligibility)
            .unwrap_or_else(|| crate::sharing::pair_eligibility(db, normal, test, both))
    }

    pub(super) fn prewarm(&self, db: &dyn HirDatabase) {
        if self.is_empty() || self.snapshot.is_some() {
            return;
        }
        let tally = super::backend::Tally::global();
        for &(normal, test, both) in &self.pairs {
            tally.step(super::Step::TwinIndex, || hir_def::twins::twin_index(db, normal, test));
            tally.step(super::Step::Eligibility, || {
                crate::sharing::pair_eligibility(db, normal, test, both)
            });
        }
    }

    pub(super) fn decisions(&self, db: &dyn HirDatabase) -> Vec<u128> {
        if self.is_empty() {
            return Vec::new();
        }
        if let Some(snapshot) = &self.snapshot {
            return snapshot.0.iter().map(|it| it.key.3).collect();
        }
        self.pairs.iter().map(|&(n, t, both)| decision_serial(db, n, t, both)).collect()
    }

    pub fn new(pairs: Vec<(Crate, Crate, bool)>) -> Self {
        Self { pairs, enabled: true, snapshot: None }
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
            let eligibility = self.eligibility(db, normal, test, both);
            if eligibility.pair_veto.is_empty() && eligibility.candidates.contains(&item) {
                return self.twins(db, normal, test).twins.get(&item).copied().unwrap_or(item);
            }
        }
        item
    }

    pub(super) fn analysis_shared(&self, db: &dyn HirDatabase, func: FunctionId) -> bool {
        self.pairs.iter().any(|&(n, t, both)| {
            func.krate(db) == t
                && self.eligibility(db, n, t, both).analysis_shared.contains(&func.into())
        })
    }

    pub(super) fn analysis_source(
        &self,
        db: &dyn HirDatabase,
        func: FunctionId,
    ) -> Option<FunctionId> {
        if self.is_empty() || !self.analysis_shared(db, func) {
            return None;
        }
        for &(normal, test, both) in &self.pairs {
            if func.krate(db) == test
                && self.eligibility(db, normal, test, both).pair_veto.is_empty()
                && let Some(&AttrDefId::FunctionId(source)) =
                    self.twins(db, normal, test).twins.get(&func.into())
            {
                return Some(source);
            }
        }
        None
    }

    pub(super) fn analysis_fold<'db, T: TypeFoldable<DbInterner<'db>>>(
        &self,
        db: &'db dyn HirDatabase,
        source: FunctionId,
        value: T,
    ) -> T {
        value.fold_with(&mut Canonical {
            db,
            sharing: self,
            interner: DbInterner::new_with(db, source.krate(db)),
            reverse: false,
            analysis: Some(source.krate(db)),
            opaque_only: false,
        })
    }

    pub(super) fn body_source(&self, db: &dyn HirDatabase, func: FunctionId) -> Option<FunctionId> {
        self.analysis_source(db, func).or_else(|| {
            let canonical = self.function(db, func);
            (canonical != func).then_some(canonical)
        })
    }

    pub(super) fn reuse_opaques<'db, T: TypeFoldable<DbInterner<'db>>>(
        &self,
        db: &'db dyn HirDatabase,
        krate: Crate,
        value: T,
    ) -> T {
        value.fold_with(&mut Canonical {
            db,
            sharing: self,
            interner: DbInterner::new_with(db, krate),
            reverse: false,
            analysis: None,
            opaque_only: true,
        })
    }

    pub(super) fn analysis_item(
        &self,
        db: &dyn HirDatabase,
        source: FunctionId,
        item: AttrDefId,
    ) -> AttrDefId {
        let normal = source.krate(db);
        for &(n, t, _) in &self.pairs {
            if n == normal && item.module(db).krate(db) == n {
                return self.reverse(db, n, t).get(&item).copied().unwrap_or(item);
            }
        }
        item
    }

    pub(super) fn analysis_instance(
        &self,
        db: &dyn HirDatabase,
        def: InstanceDef,
    ) -> Option<(FunctionId, InstanceDef)> {
        use salsa::plumbing::{AsId, FromId};
        let owner = match def {
            InstanceDef::Fn(f) => {
                return self.body_source(db, f).map(|source| (source, InstanceDef::Fn(source)));
            }
            InstanceDef::Closure(id) => InternedClosureId::from_id(id).loc(db).owner,
            InstanceDef::Coroutine(id) | InstanceDef::CoroutineByMove(id) => {
                InternedCoroutineId::from_id(id).loc(db).owner
            }
            _ => return None,
        };
        let InferBodyId::DefWithBodyId(DefWithBodyId::FunctionId(func)) = owner else {
            return None;
        };
        let source = self.body_source(db, func)?;
        let def = match def {
            InstanceDef::Closure(id) => {
                let mut loc = InternedClosureId::from_id(id).loc(db);
                loc.owner = source.into();
                InstanceDef::Closure(InternedClosureId::new(db, loc).as_id())
            }
            InstanceDef::Coroutine(id) | InstanceDef::CoroutineByMove(id) => {
                let mut loc = InternedCoroutineId::from_id(id).loc(db);
                loc.owner = source.into();
                let id = InternedCoroutineId::new(db, loc).as_id();
                if matches!(def, InstanceDef::CoroutineByMove(_)) {
                    InstanceDef::CoroutineByMove(id)
                } else {
                    InstanceDef::Coroutine(id)
                }
            }
            _ => return None,
        };
        Some((source, def))
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
            analysis: None,
            opaque_only: false,
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
            analysis: None,
            opaque_only: false,
        })
    }

    pub(super) fn coroutine_is_by_move<'db>(
        &self,
        db: &'db dyn HirDatabase,
        id: InternedCoroutineId<'db>,
        args: rustc_type_ir::CoroutineArgs<DbInterner<'db>>,
    ) -> bool {
        use salsa::plumbing::{AsId, FromId};
        let id = match self.analysis_instance(db, InstanceDef::Coroutine(id.as_id())) {
            Some((_, InstanceDef::Coroutine(source))) => InternedCoroutineId::from_id(source),
            _ => id,
        };
        crate::mir::is_by_move_coroutine(db, id, args)
    }

    fn link_item(&self, db: &dyn HirDatabase, item: AttrDefId) -> AttrDefId {
        for &(normal, test, both) in &self.pairs {
            if !both && item.module(db).krate(db) == normal {
                if let Some(&t) = self.reverse(db, normal, test).get(&item) {
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
        super::backend::Tally::global()
            .step(super::Step::Canonicalize, || self.canonical_instance(db, instance))
    }

    fn canonical_instance(&self, db: &dyn HirDatabase, instance: &Instance) -> Instance {
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
        let home = super::home::Homes::default().home(db, instance, env);
        if home.krate == env.krate {
            return env.clone();
        }
        let env = env.as_ref(db);
        let krate = home.krate;
        ParamEnvAndCrate { krate, param_env: self.fold(db, krate, env.param_env) }.store()
    }

    pub(super) fn needs_policy(&self, db: &dyn HirDatabase, instance: &Instance) -> bool {
        let mut types = TestTypes { db, sharing: self, found: false };
        instance.args.as_ref().visit_with(&mut types);
        types.found || self.test_body(db, instance)
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
                    self.twins(db, normal, test).twins.iter().find(|(_, n)| **n == id.into())
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
                if let Some(&AttrDefId::FunctionId(t)) =
                    self.reverse(db, normal, test).get(&func.into())
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
    analysis: Option<Crate>,
    opaque_only: bool,
}

impl<'db> Canonical<'_, 'db> {
    fn item(&self, item: AttrDefId) -> AttrDefId {
        if self.opaque_only {
            return item;
        }
        if let Some(normal) = self.analysis {
            for &(n, t, _) in &self.sharing.pairs {
                if n == normal && item.module(self.db).krate(self.db) == n {
                    return self.sharing.reverse(self.db, n, t).get(&item).copied().unwrap_or(item);
                }
            }
            return item;
        }
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
            TyKind::CoroutineClosure(id, args) => {
                let mut loc = id.0.loc(self.db);
                loc.owner = self.owner(loc.owner);
                return Ty::new_coroutine_closure(
                    self.interner,
                    InternedCoroutineClosureId::new(self.db, loc).into(),
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
                let twins = self.sharing.twins(self.db, normal, test);
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
