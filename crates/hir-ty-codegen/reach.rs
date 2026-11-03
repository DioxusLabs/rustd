//! What a function can run: its own code and the code of everything it refers to, as one
//! number. Two builds in which a test has the same print run the same instructions over the
//! same constant data when they call it, so it has the same result, as far as code decides.

use base_db::{Crate, CrateOrigin, LangCrateOrigin};
use hir_def::{
    AdtId, FunctionId, HasModule, ItemContainerId, Lookup, StaticId,
    signatures::{FunctionSignature, StaticSignature, StructSignature},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::inherent::IntoKind as _;
use std::sync::Arc;

use crate::next_solver::TyKind;

use crate::{db::HirDatabase, traits::StoredParamEnvAndCrate};

use super::{
    CodegenError, Instance, InstanceDef, compiled_static,
    fragment::{DataRequest, FuncTarget, Requests},
    is_thread_local,
    patch::Mark,
    print_of, static_serial,
};

#[path = "reach_dynamic.rs"]
mod dynamic;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Node {
    Root(FunctionId),
    Instance(Instance, StoredParamEnvAndCrate),
    Static(StaticId),
}

/// What a test can run and what it shares with the other tests of its program.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Reached {
    /// `None` when something it reaches did not compile: what that calls is not known.
    pub print: Option<u128>,
    /// Equal for tests that reach a static the program can write, directly or through a
    /// chain of tests that do: one of them can leave there what another finds.
    pub group: usize,
}

impl Node {
    fn name(&self, db: &dyn HirDatabase) -> String {
        match self {
            Node::Root(func) | Node::Instance(Instance { def: InstanceDef::Fn(func), .. }, _) => {
                FunctionSignature::of(db, *func).name.as_str().to_owned()
            }
            Node::Instance(instance, _) => format!("{:?}", instance.def),
            Node::Static(id) => StaticSignature::of(db, *id).name.as_str().to_owned(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Graph {
    sharing: super::Sharing,
    ids: FxHashMap<Node, usize>,
    nodes: Vec<Node>,
    edges: Vec<Vec<usize>>,
    /// The statics among the nodes that a running program can change.
    written: Vec<usize>,
    /// The crates an edit can change the code of.
    edited: Arc<[Crate]>,
    /// The first nodes that did not compile, and why.
    unknown: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Input {
    sharing: super::Sharing,
    edited: Arc<[Crate]>,
    tests: Vec<FunctionId>,
    always: Vec<FunctionId>,
    kept: Vec<StaticId>,
}

#[salsa::interned(debug, unsafe(no_lifetime), revisions = usize::MAX)]
struct ReachInput {
    #[returns(ref)]
    data: Arc<Input>,
}

#[salsa::interned(debug, unsafe(no_lifetime), revisions = usize::MAX)]
struct Component {
    #[returns(ref)]
    members: Vec<Node>,
    #[returns(ref)]
    below: Vec<Component>,
}

/// A deduplicated reach set, chunked independently of call edges.
#[salsa::interned(debug, unsafe(no_lifetime), revisions = usize::MAX)]
struct PrintTree {
    #[returns(ref)]
    members: Vec<Component>,
    #[returns(ref)]
    children: Vec<PrintTree>,
}

fn print_tree(db: &dyn HirDatabase, roots: &[Component]) -> PrintTree {
    let mut seen = FxHashSet::default();
    let mut pending = roots.to_vec();
    while let Some(component) = pending.pop() {
        if seen.insert(component) {
            pending.extend(component.below(db));
        }
    }
    let mut members: Vec<_> = seen.into_iter().map(|it| (print_of(&it), it)).collect();
    members.sort_by_key(|it| it.0);
    print_subtree(db, &members, 128)
}

fn print_subtree(db: &dyn HirDatabase, members: &[(u128, Component)], bits: u32) -> PrintTree {
    if members.len() <= 32 || bits == 0 {
        return PrintTree::new(db, members.iter().map(|it| it.1).collect::<Vec<_>>(), Vec::new());
    }
    let bits = bits.saturating_sub(5);
    // Fixed hash prefixes let overlapping reach sets share their unchanged subtrees.
    let mut children = Vec::new();
    let mut rest = members;
    while let Some(&(key, _)) = rest.first() {
        let end = rest.partition_point(|it| it.0 >> bits == key >> bits);
        children.push(print_subtree(db, &rest[..end], bits));
        rest = &rest[end..];
    }
    PrintTree::new(db, Vec::new(), children)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Edges {
    targets: Vec<Node>,
    written: bool,
    unknown: Option<String>,
}

fn settled(db: &dyn HirDatabase, node: &Node, edited: &[Crate]) -> bool {
    let krate = match node {
        Node::Root(func) => func.krate(db),
        Node::Instance(Instance { def: InstanceDef::Fn(func), args, .. }, _)
            if args.as_ref().iter().all(|it| it.region().is_some()) =>
        {
            func.krate(db)
        }
        Node::Instance(..) => return false,
        Node::Static(id) => id.krate(db),
    };
    !edited.contains(&krate)
}

fn compiled<'db>(
    db: &'db dyn HirDatabase,
    node: &Node,
    sharing: &super::Sharing,
) -> Result<(u128, &'db Requests), &'db CodegenError> {
    match node {
        Node::Root(func) => super::program_root(db, *func, sharing)
            .as_ref()
            .map(|it| (super::program_root_serial(db, *func, sharing.clone()), &it.requests)),
        Node::Instance(instance, env) => {
            super::program_instance(db, instance.clone(), env.clone(), sharing).as_ref().map(|it| {
                (
                    super::program_instance_serial(
                        db,
                        instance.clone(),
                        env.clone(),
                        sharing.clone(),
                    ),
                    &it.requests,
                )
            })
        }
        Node::Static(id) => {
            compiled_static(db, *id).as_ref().map(|it| (static_serial(db, *id), &it.requests))
        }
    }
}

#[salsa::tracked(returns(ref))]
fn reach_edges(
    db: &dyn HirDatabase,
    node: Node,
    sharing: super::Sharing,
    edited: Arc<[Crate]>,
) -> Edges {
    let mut result = Edges { targets: Vec::new(), written: false, unknown: None };
    if settled(db, &node, &edited) || foreign(db, &node) {
        return result;
    }
    if let Node::Static(id) = node {
        result.written = is_thread_local(db, id)
            || compiled_static(db, id).as_ref().map_or(true, |it| it.writable);
    }
    let (_, requests) = match compiled(db, &node, &sharing) {
        Ok(it) => it,
        Err(why) => {
            if !matches!(&node, Node::Instance(it, _) if names_type_id(db, it)) {
                result.unknown = Some(format!("{}: {why:?}", node.name(db)));
            }
            return result;
        }
    };
    let mut homes = super::home::Homes::default();
    result.targets.extend(requests.funcs.iter().filter_map(|it| match &it.target {
        FuncTarget::Instance(instance, env) => Some(match instance.def {
            InstanceDef::Fn(func) if instance.args.as_ref().is_empty() => Node::Root(func),
            _ => Node::Instance(instance.clone(), homes.home(db, instance, env)),
        }),
        FuncTarget::Symbol(_) | FuncTarget::Path(_) | FuncTarget::Asm(_) => None,
    }));
    result.targets.extend(requests.datas.iter().filter_map(|it| match it {
        DataRequest::Static(id) => Some(Node::Static(*id)),
        _ => None,
    }));
    result.targets.sort_by_key(print_of);
    result.targets.dedup();
    result
}

#[salsa::tracked(returns(copy))]
fn reach_own(
    db: &dyn HirDatabase,
    node: Node,
    sharing: super::Sharing,
    edited: Arc<[Crate]>,
) -> Option<u128> {
    if settled(db, &node, &edited) || foreign(db, &node) {
        return Some(0);
    }
    match compiled(db, &node, &sharing) {
        Ok((serial, requests)) => Some(print_of(&Mark::new(db, serial, requests).seen())),
        Err(_) => matches!(&node, Node::Instance(it, _) if names_type_id(db, it)).then_some(0),
    }
}

/// Whether the instance is `core::any::TypeId::of::<T>`.
fn names_type_id(db: &dyn HirDatabase, instance: &Instance) -> bool {
    let InstanceDef::Fn(func) = instance.def else { return false };
    let ItemContainerId::ImplId(impl_) = func.lookup(db).container else { return false };
    let TyKind::Adt(adt, _) = db.impl_self_ty(impl_).skip_binder().kind() else { return false };
    let AdtId::StructId(id) = adt.def_id() else { return false };
    FunctionSignature::of(db, func).name.as_str() == "of"
        && StructSignature::of(db, id).name.as_str() == "TypeId"
        && matches!(func.krate(db).data(db).origin, CrateOrigin::Lang(LangCrateOrigin::Core))
}

/// Whether the node is a function of an `extern` block: a name the linker resolves, to code
/// rustc compiled or to an exported function, which the caller hands in as always reached.
fn foreign(db: &dyn HirDatabase, node: &Node) -> bool {
    let (Node::Root(func) | Node::Instance(Instance { def: InstanceDef::Fn(func), .. }, _)) = node
    else {
        return false;
    };
    matches!(func.lookup(db).container, ItemContainerId::ExternBlockId(_))
}

impl Graph {
    /// The node and everything it refers to, added when they are not there yet.
    fn node(&mut self, db: &dyn HirDatabase, node: Node) -> usize {
        if let Some(&id) = self.ids.get(&node) {
            return id;
        }
        let first = self.nodes.len();
        let mut stack = vec![(first, self.add(db, node).into_iter())];
        while let Some((id, targets)) = stack.last_mut() {
            let id = *id;
            let Some(target) = targets.next() else {
                stack.pop();
                continue;
            };
            let known = self.ids.get(&target).copied();
            let target = known.unwrap_or_else(|| {
                let new = self.nodes.len();
                stack.push((new, self.add(db, target).into_iter()));
                new
            });
            self.edges[id].push(target);
        }
        first
    }

    /// Takes the node in and says what it refers to.
    fn add(&mut self, db: &dyn HirDatabase, node: Node) -> Vec<Node> {
        let id = self.nodes.len();
        self.ids.insert(node.clone(), id);
        self.nodes.push(node.clone());
        self.edges.push(Vec::new());
        let edges = reach_edges(db, node, self.sharing.clone(), self.edited.clone());
        if edges.written {
            self.written.push(id);
        }
        if let Some(unknown) = &edges.unknown
            && self.unknown.len() < 8
        {
            self.unknown.push(unknown.clone());
        }
        edges.targets.clone()
    }
    /// The strongly connected components, each after the ones it refers to, and the
    /// component of each node.
    fn components(&self) -> (Vec<Vec<usize>>, Vec<usize>) {
        const NONE: usize = usize::MAX;
        let count = self.edges.len();
        let (mut index, mut low) = (vec![NONE; count], vec![0; count]);
        let mut of = vec![NONE; count];
        let mut components: Vec<Vec<usize>> = Vec::new();
        let (mut open, mut next) = (Vec::new(), 0);
        for root in 0..count {
            if index[root] != NONE {
                continue;
            }
            let mut stack = vec![(root, 0)];
            while let Some(&mut (node, ref mut edge)) = stack.last_mut() {
                if *edge == 0 {
                    (index[node], low[node]) = (next, next);
                    next += 1;
                    open.push(node);
                }
                if let Some(&target) = self.edges[node].get(*edge) {
                    *edge += 1;
                    if index[target] == NONE {
                        stack.push((target, 0));
                    } else if of[target] == NONE {
                        low[node] = low[node].min(index[target]);
                    }
                    continue;
                }
                stack.pop();
                if let Some(&(parent, _)) = stack.last() {
                    low[parent] = low[parent].min(low[node]);
                }
                if low[node] == index[node] {
                    let at = open.iter().rposition(|&it| it == node).expect("opened above");
                    let members = open.split_off(at);
                    members.iter().for_each(|&it| of[it] = components.len());
                    components.push(members);
                }
            }
        }
        (components, of)
    }
}

/// A set of small numbers.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Bits(Vec<u64>);

impl Bits {
    fn contains(&self, at: usize) -> bool {
        self.0.get(at / 64).is_some_and(|word| word >> (at % 64) & 1 == 1)
    }
    fn insert(&mut self, at: usize) {
        if self.0.len() <= at / 64 {
            self.0.resize(at / 64 + 1, 0);
        }
        self.0[at / 64] |= 1 << (at % 64);
    }

    fn union(&mut self, other: &Bits) {
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), 0);
        }
        self.0.iter_mut().zip(&other.0).for_each(|(a, b)| *a |= b);
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let words = self.0.iter().enumerate();
        words.flat_map(|(at, word)| {
            (0..64).filter(move |bit| word >> bit & 1 == 1).map(move |bit| at * 64 + bit)
        })
    }
}

/// For each of `tests`, what it can run, where an edit reaches the crates `edited` and no
/// others. `always` and `kept` are what runs or is found without any code naming it: every
/// test is taken to reach them. With it, the print of what all of them reach, and the first
/// things reached that did not compile.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Topology {
    graph: Graph,
    components: Vec<Component>,
    of: Vec<usize>,
    tests: Vec<usize>,
    ambient: Vec<usize>,
    groups: Vec<usize>,
}

#[salsa::tracked(returns(ref))]
fn reach_topology(db: &dyn HirDatabase, input: ReachInput) -> Topology {
    let input = input.data(db);
    let mut graph =
        Graph { sharing: input.sharing.clone(), edited: input.edited.clone(), ..Graph::default() };
    let tests: Vec<usize> = input.tests.iter().map(|&it| graph.node(db, Node::Root(it))).collect();
    let mut ambient: Vec<usize> =
        input.always.iter().map(|&it| graph.node(db, Node::Root(it))).collect();
    ambient.extend(input.kept.iter().map(|&it| graph.node(db, Node::Static(it))));
    let (components, of) = graph.components();
    let written: FxHashMap<usize, usize> =
        graph.written.iter().enumerate().map(|(at, &node)| (node, at)).collect();
    // Per component: its dependencies and the written statics among them.
    let mut reachable = Vec::with_capacity(components.len());
    let mut shared: Vec<Bits> = Vec::with_capacity(components.len());
    for (at, members) in components.iter().enumerate() {
        let mut below: Vec<usize> =
            members.iter().flat_map(|&it| &graph.edges[it]).map(|&it| of[it]).collect();
        below.sort_unstable();
        below.dedup();
        below.retain(|&it| it != at);
        let mut statics = Bits::default();
        members.iter().filter_map(|it| written.get(it)).for_each(|&it| statics.insert(it));
        for &it in &below {
            statics.union(&shared[it]);
        }
        let mut members: Vec<_> = members.iter().map(|&it| graph.nodes[it].clone()).collect();
        members.sort_by_key(print_of);
        let mut below: Vec<_> = below.into_iter().map(|id| reachable[id]).collect();
        below.sort_by_key(print_of);
        reachable.push(Component::new(db, members, below));
        shared.push(statics);
    }
    let mut ambient_shared = Bits::default();
    ambient.iter().for_each(|&it| ambient_shared.union(&shared[of[it]]));
    // The tests that reach a static in common are one group.
    let mut owner: FxHashMap<usize, usize> = FxHashMap::default();
    let mut group: Vec<usize> = (0..tests.len()).collect();
    fn find(group: &mut [usize], mut at: usize) -> usize {
        while group[at] != at {
            group[at] = group[group[at]];
            at = group[at];
        }
        at
    }
    for (at, &test) in tests.iter().enumerate() {
        for it in shared[of[test]].iter().chain(ambient_shared.iter()) {
            let other = *owner.entry(it).or_insert(at);
            let (a, b) = (find(&mut group, at), find(&mut group, other));
            group[a.max(b)] = a.min(b);
        }
    }
    let group: Vec<usize> = (0..tests.len()).map(|at| find(&mut group, at)).collect();
    Topology { graph, components: reachable, of, tests, ambient, groups: group }
}

#[salsa::tracked(returns(copy))]
fn reach_component_print(
    db: &dyn HirDatabase,
    component: Component,
    sharing: super::Sharing,
    edited: Arc<[Crate]>,
) -> Option<u128> {
    let mut own: Option<Vec<u128>> = component
        .members(db)
        .iter()
        .map(|node| reach_own(db, node.clone(), sharing.clone(), edited.clone()))
        .collect();
    if let Some(own) = &mut own {
        own.sort_unstable();
    }
    own.map(|it| print_of(&it))
}

#[salsa::tracked(returns(copy))]
fn reach_tree_print(
    db: &dyn HirDatabase,
    tree: PrintTree,
    sharing: super::Sharing,
    edited: Arc<[Crate]>,
) -> Option<u128> {
    let mut sum = 0u128;
    for &component in tree.members(db) {
        sum = sum.wrapping_add(reach_component_print(
            db,
            component,
            sharing.clone(),
            edited.clone(),
        )?);
    }
    for &child in tree.children(db) {
        sum = sum.wrapping_add(reach_tree_print(db, child, sharing.clone(), edited.clone())?);
    }
    Some(sum)
}

#[salsa::tracked(returns(ref))]
fn reach_ambient_components(db: &dyn HirDatabase, input: ReachInput) -> Vec<Component> {
    let topology = reach_topology(db, input);
    topology.ambient.iter().map(|&id| topology.components[topology.of[id]]).collect()
}

#[salsa::tracked(returns(copy))]
fn reach_ambient_tree(db: &dyn HirDatabase, input: ReachInput) -> PrintTree {
    print_tree(db, reach_ambient_components(db, input))
}

#[salsa::tracked(returns(ref))]
fn reach_ambient(db: &dyn HirDatabase, input: ReachInput) -> Option<Vec<u128>> {
    reach_tree_print(
        db,
        reach_ambient_tree(db, input),
        input.data(db).sharing.clone(),
        input.data(db).edited.clone(),
    )
    .map(|print| vec![print])
}

#[salsa::tracked(returns(copy))]
fn reach_root_component(db: &dyn HirDatabase, input: ReachInput, test: usize) -> Component {
    let topology = reach_topology(db, input);
    topology.components[topology.of[topology.tests[test]]]
}

#[salsa::tracked(returns(copy))]
fn reach_root_tree(db: &dyn HirDatabase, input: ReachInput, test: usize) -> PrintTree {
    print_tree(db, &[reach_root_component(db, input, test)])
}

#[salsa::tracked(returns(copy))]
fn reach_root_code(db: &dyn HirDatabase, input: ReachInput, test: usize) -> Option<u128> {
    reach_tree_print(
        db,
        reach_root_tree(db, input, test),
        input.data(db).sharing.clone(),
        input.data(db).edited.clone(),
    )
}

#[salsa::tracked(returns(copy))]
fn reach_root_print(db: &dyn HirDatabase, input: ReachInput, test: usize) -> Option<u128> {
    reach_root_code(db, input, test).zip(reach_ambient(db, input).as_ref()).map(|it| print_of(&it))
}

pub fn reached(
    db: &dyn HirDatabase,
    sharing: super::Sharing,
    mut edited: FxHashSet<Crate>,
    tests: &[FunctionId],
    always: &[FunctionId],
    kept: &[StaticId],
) -> (Vec<Reached>, Option<u128>, Vec<String>) {
    sharing.edited_crates(&mut edited);
    let mut edited: Vec<_> = edited.into_iter().collect();
    edited.sort_by_key(print_of);
    let input = ReachInput::new(
        db,
        Arc::new(Input {
            sharing,
            edited: edited.into(),
            tests: tests.to_vec(),
            always: always.to_vec(),
            kept: kept.to_vec(),
        }),
    );
    reach_program(db, input).clone()
}

type Answer = (Vec<Reached>, Option<u128>, Vec<String>);

#[derive(Default, Clone)]
pub(super) struct Cache {
    state: Option<Arc<Snapshot>>,
    changed: FxHashSet<base_db::FileId>,
    patch: Option<FxHashSet<super::patch::Node>>,
    previous: FxHashSet<super::patch::Node>,
}

#[derive(Clone)]
struct Snapshot {
    input: ReachInput,
    topology: Arc<Topology>,
    nodes: Arc<FxHashMap<super::patch::Node, Vec<usize>>>,
    bodies: Arc<FxHashMap<base_db::FileId, Vec<(FunctionId, crate::sharing::BodyItems)>>>,
    edges: Arc<Vec<Edges>>,
    own: Vec<Option<u128>>,
    components: Vec<Option<u128>>,
    roots: Arc<Vec<Bits>>,
    ambient: Arc<FxHashSet<usize>>,
    code: Vec<Option<u128>>,
    ambient_code: Option<u128>,
    alone: Vec<Option<u128>>,
    groups: Arc<FxHashMap<usize, Vec<usize>>>,
    answer: Answer,
    dynamic: Option<DynamicSnapshot>,
    edges_changed: bool,
}

#[derive(Clone)]
struct DynamicSnapshot {
    graph: Graph,
    engine: dynamic::Dynamic,
    edges: Vec<Edges>,
    roots: Vec<(usize, usize)>,
    groups: Vec<usize>,
    unknown: FxHashSet<usize>,
}

impl Cache {
    pub(super) fn clear(&mut self) {
        *self = Self::default();
    }

    pub(super) fn touch(&mut self, file: base_db::FileId) {
        self.changed.insert(file);
        self.patch = None;
    }

    pub(super) fn patch(&mut self, changed: Option<FxHashSet<super::patch::Node>>) {
        let Some(changed) = changed else {
            self.clear();
            return;
        };
        let mut candidates = std::mem::replace(&mut self.previous, changed);
        candidates.extend(self.previous.iter().cloned());
        self.patch = Some(candidates);
    }

    pub(super) fn reached(
        &mut self,
        db: &dyn HirDatabase,
        sharing: super::Sharing,
        mut edited: FxHashSet<Crate>,
        tests: &[FunctionId],
        always: &[FunctionId],
        kept: &[StaticId],
        program: &str,
    ) -> Answer {
        sharing.edited_crates(&mut edited);
        let mut edited: Vec<_> = edited.into_iter().collect();
        edited.sort_by_key(print_of);
        let input = ReachInput::new(
            db,
            Arc::new(Input {
                sharing,
                edited: edited.into(),
                tests: tests.to_vec(),
                always: always.to_vec(),
                kept: kept.to_vec(),
            }),
        );
        let changed = std::mem::take(&mut self.changed);
        let patch = self.patch.take();
        let update = match &mut self.state {
            None => Err("no retained snapshot"),
            Some(state) if state.input != input => {
                let before = state.input.data(db);
                let after = input.data(db);
                Err(if before.sharing != after.sharing {
                    "sharing policy changed"
                } else if before.edited != after.edited {
                    "edited crates changed"
                } else if before.tests != after.tests {
                    "test roots changed"
                } else if before.always != after.always {
                    "always-reached roots changed"
                } else {
                    "kept statics changed"
                })
            }
            Some(state) => Arc::make_mut(state).update(db, &changed, patch.as_ref(), program),
        };
        if update.is_ok() {
            let state = self.state.as_ref().unwrap();
            if std::env::var_os("RUSTD_VERIFY_FASTPATH").is_some_and(|it| it == "1") {
                assert_eq!(&state.answer, reach_program(db, input), "reach fast path");
            }
            if std::env::var_os("RUSTD_STATS").is_some() {
                let path = if state.edges_changed { "updated edges" } else { "unchanged edges" };
                eprintln!("reach fast path: {path}; program={program}");
            }
            return state.answer.clone();
        }
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!("reach full path: {}; program={program}", update.unwrap_err());
        }
        let answer = reach_program(db, input).clone();
        self.state = Some(Arc::new(Snapshot::new(db, input, answer.clone())));
        answer
    }
}

impl Snapshot {
    fn new(db: &dyn HirDatabase, input: ReachInput, answer: Answer) -> Self {
        let data = input.data(db);
        let topology = Arc::new(reach_topology(db, input).clone());
        let mut nodes: FxHashMap<_, Vec<usize>> = FxHashMap::default();
        let mut functions: FxHashSet<FunctionId> = FxHashSet::default();
        let mut edges = Vec::new();
        let mut own = Vec::new();
        for (id, node) in topology.graph.nodes.iter().enumerate() {
            if let Some(func) = match node {
                Node::Root(func) => Some(*func),
                Node::Instance(instance, _) => super::home::written_in(db, instance),
                Node::Static(_) => None,
            } {
                functions.insert(func);
            }
            let key = match node {
                Node::Root(id) => super::patch::Node::Root(*id),
                Node::Static(id) => super::patch::Node::Static(*id),
                Node::Instance(instance, _) => super::patch::Node::Instance(instance.clone()),
            };
            nodes.entry(key).or_default().push(id);
            edges.push(
                reach_edges(db, node.clone(), data.sharing.clone(), data.edited.clone()).clone(),
            );
            own.push(reach_own(db, node.clone(), data.sharing.clone(), data.edited.clone()));
        }
        let ids: FxHashMap<_, _> =
            topology.components.iter().copied().enumerate().map(|(i, c)| (c, i)).collect();
        let mut roots = vec![Bits::default(); topology.components.len()];
        for (root, &node) in topology.tests.iter().enumerate() {
            roots[topology.of[node]].insert(root);
        }
        let mut ambient: FxHashSet<_> =
            topology.ambient.iter().map(|&node| topology.of[node]).collect();
        for (id, component) in topology.components.iter().enumerate().rev() {
            let here = roots[id].clone();
            for below in component.below(db) {
                let below = ids[below];
                roots[below].union(&here);
                if ambient.contains(&id) {
                    ambient.insert(below);
                }
            }
        }
        let components = topology
            .components
            .iter()
            .map(|&c| reach_component_print(db, c, data.sharing.clone(), data.edited.clone()))
            .collect();
        let code = (0..data.tests.len()).map(|id| reach_root_code(db, input, id)).collect();
        let ambient_code = reach_ambient(db, input).as_ref().map(|it| it[0]);
        let alone = (0..data.tests.len()).map(|id| reach_root_print(db, input, id)).collect();
        let mut groups: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for (root, &group) in topology.groups.iter().enumerate() {
            groups.entry(group).or_default().push(root);
        }
        let mut bodies: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for func in functions {
            if hir_def::signatures::FunctionSignature::of(db, func).has_body() {
                bodies
                    .entry(super::home::body_file(db, func.into()))
                    .or_default()
                    .push((func, crate::sharing::body_item_inventory(db, func).clone()));
            }
        }
        Self {
            input,
            topology,
            nodes: Arc::new(nodes),
            bodies: Arc::new(bodies),
            edges: Arc::new(edges),
            own,
            components,
            roots: Arc::new(roots),
            ambient: Arc::new(ambient),
            code,
            ambient_code,
            alone,
            groups: Arc::new(groups),
            answer,
            dynamic: None,
            edges_changed: false,
        }
    }

    fn update_dynamic(
        &mut self,
        db: &dyn HirDatabase,
        candidates: &FxHashSet<usize>,
        program: &str,
    ) {
        let data = self.input.data(db);
        let count = data.tests.len();
        let state = self.dynamic.get_or_insert_with(|| {
            let graph = self.topology.graph.clone();
            let mut roots: Vec<_> = self
                .topology
                .tests
                .iter()
                .copied()
                .enumerate()
                .map(|(root, node)| (node, root))
                .collect();
            roots.extend(self.topology.ambient.iter().map(|&node| (node, count)));
            let engine =
                dynamic::Dynamic::new(graph.edges.clone(), self.own.clone(), &roots, count + 1);
            DynamicSnapshot {
                graph,
                engine,
                edges: self.edges.as_ref().clone(),
                roots,
                groups: self.topology.groups.clone(),
                unknown: self
                    .edges
                    .iter()
                    .enumerate()
                    .filter_map(|(id, edges)| edges.unknown.is_some().then_some(id))
                    .collect(),
            }
        });
        state.engine.affected = Bits::default();
        let mut pending: Vec<_> = candidates.iter().copied().collect();
        let mut pulled = FxHashSet::default();
        let mut changes = Vec::new();
        let mut added = state.graph.nodes.len();
        while let Some(id) = pending.pop() {
            if !pulled.insert(id) {
                continue;
            }
            let node = state.graph.nodes[id].clone();
            let edges =
                reach_edges(db, node.clone(), data.sharing.clone(), data.edited.clone()).clone();
            let own = reach_own(db, node, data.sharing.clone(), data.edited.clone());
            let targets: Vec<_> =
                edges.targets.iter().map(|node| state.graph.node(db, node.clone())).collect();
            while added < state.graph.nodes.len() {
                let node = state.graph.nodes[added].clone();
                let edges =
                    reach_edges(db, node.clone(), data.sharing.clone(), data.edited.clone())
                        .clone();
                let own = reach_own(db, node.clone(), data.sharing.clone(), data.edited.clone());
                assert_eq!(state.engine.add_node(own), added);
                if edges.unknown.is_some() {
                    state.unknown.insert(added);
                }
                state.edges.push(edges);
                let (key, func) = match node {
                    Node::Root(id) => (super::patch::Node::Root(id), Some(id)),
                    Node::Instance(instance, _) => {
                        let func = super::home::written_in(db, &instance);
                        (super::patch::Node::Instance(instance), func)
                    }
                    Node::Static(id) => (super::patch::Node::Static(id), None),
                };
                Arc::make_mut(&mut self.nodes).entry(key).or_default().push(added);
                if let Some(func) = func.filter(|&func| FunctionSignature::of(db, func).has_body())
                {
                    let bodies = Arc::make_mut(&mut self.bodies)
                        .entry(super::home::body_file(db, func.into()))
                        .or_default();
                    if !bodies.iter().any(|&(id, _)| id == func) {
                        bodies.push((func, crate::sharing::body_item_inventory(db, func).clone()));
                    }
                }
                pending.push(added);
                added += 1;
            }
            if state.engine.edges[id] != targets
                || state.edges[id].written != edges.written
                || state.edges[id].unknown != edges.unknown
            {
                self.edges_changed = true;
            }
            if edges.unknown.is_some() {
                state.unknown.insert(id);
            } else {
                state.unknown.remove(&id);
            }
            for &target in &targets {
                if state.engine.masks[state.engine.owner[target]].iter().next().is_none() {
                    pending.push(target);
                }
            }
            if edges.written != state.edges[id].written {
                state.graph.written.retain(|&node| node != id);
                if edges.written {
                    state.graph.written.push(id);
                }
            }
            state.graph.edges[id] = targets.clone();
            state.edges[id] = edges;
            state.engine.set_own(id, own);
            changes.push((id, targets));
        }
        let mut seeds = Vec::new();
        for (id, targets) in changes {
            state.engine.change_edges(id, targets, &state.roots, &mut seeds);
        }
        state.engine.settle(seeds);
        let mut changed_groups = FxHashSet::default();
        if self.edges_changed {
            let new_groups = dynamic_groups(&state.graph.written, &state.engine, count);
            for (root, (&old, &new)) in state.groups.iter().zip(&new_groups).enumerate() {
                if old != new || state.engine.affected.contains(root) {
                    changed_groups.insert(old);
                    changed_groups.insert(new);
                }
            }
            state.groups = new_groups;
            let mut groups: FxHashMap<_, Vec<_>> = FxHashMap::default();
            for (root, &group) in state.groups.iter().enumerate() {
                groups.entry(group).or_default().push(root);
            }
            self.groups = Arc::new(groups);
            self.answer
                .0
                .iter_mut()
                .zip(&state.groups)
                .for_each(|(answer, &group)| answer.group = group);
            if !self.answer.2.is_empty() || !state.unknown.is_empty() {
                let mut seen = FxHashSet::default();
                let mut pending: Vec<_> = self
                    .topology
                    .tests
                    .iter()
                    .chain(&self.topology.ambient)
                    .copied()
                    .rev()
                    .collect();
                self.answer.2.clear();
                while let Some(id) = pending.pop() {
                    if !seen.insert(id) {
                        continue;
                    }
                    if let Some(unknown) = &state.edges[id].unknown {
                        self.answer.2.push(unknown.clone());
                        if self.answer.2.len() == 8 {
                            break;
                        }
                    }
                    pending.extend(state.graph.edges[id].iter().rev().copied());
                }
            }
        }
        let ambient = state.engine.code(count).map(|code| vec![code]);
        let ambient_changed = self.answer.1 != ambient.as_ref().map(print_of);
        let affected: Vec<_> = if ambient_changed {
            (0..count).collect()
        } else {
            state.engine.affected.iter().filter(|&root| root < count).collect()
        };
        let mut groups: FxHashSet<_> =
            changed_groups.into_iter().filter(|group| self.groups.contains_key(group)).collect();
        for &root in &affected {
            self.alone[root] =
                state.engine.code(root).zip(ambient.as_ref()).map(|it| print_of(&it));
            groups.insert(state.groups[root]);
        }
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!(
                "reach incremental graph: pulled={} roots={} groups={}; program={program}",
                pulled.len(),
                affected.len(),
                groups.len()
            );
        }
        refresh_groups(&self.groups, &self.alone, groups, &mut self.answer.0);
        self.answer.1 = ambient.as_ref().map(print_of);
    }

    fn update(
        &mut self,
        db: &dyn HirDatabase,
        files: &FxHashSet<base_db::FileId>,
        patch: Option<&FxHashSet<super::patch::Node>>,
        program: &str,
    ) -> Result<(), &'static str> {
        self.edges_changed = false;
        let data = self.input.data(db);
        if !files.is_empty() && patch.is_none() {
            return Err("patch candidates unavailable");
        }
        for file in files {
            if self
                .bodies
                .get(file)
                .into_iter()
                .flatten()
                .any(|(func, items)| crate::sharing::body_item_inventory(db, *func) != items)
            {
                return Err("body item inventory changed");
            }
        }
        let candidates: FxHashSet<_> = patch
            .into_iter()
            .flatten()
            .flat_map(|node| self.nodes.get(node).into_iter().flatten().copied())
            .collect();
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!("reach patch candidates: {}; program={program}", candidates.len());
        }
        if self.dynamic.is_some()
            || candidates.iter().any(|&id| {
                reach_edges(
                    db,
                    self.topology.graph.nodes[id].clone(),
                    data.sharing.clone(),
                    data.edited.clone(),
                ) != &self.edges[id]
            })
        {
            self.update_dynamic(db, &candidates, program);
            return Ok(());
        }
        let mut changed = FxHashSet::default();
        for id in candidates {
            let node = &self.topology.graph.nodes[id];
            let own = reach_own(db, node.clone(), data.sharing.clone(), data.edited.clone());
            if own != self.own[id] {
                self.own[id] = own;
                changed.insert(self.topology.of[id]);
            }
        }
        if changed.is_empty() {
            if std::env::var_os("RUSTD_STATS").is_some() {
                eprintln!("reach retained answer: unchanged component prints; program={program}");
            }
            return Ok(());
        }
        let mut affected = Bits::default();
        let before_ambient = self.ambient_code;
        for id in changed {
            let mut own: Option<Vec<_>> = self.topology.components[id]
                .members(db)
                .iter()
                .map(|node| self.own[self.topology.graph.ids[node]])
                .collect();
            if let Some(own) = &mut own {
                own.sort_unstable();
            }
            let new = own.map(|own| print_of(&own));
            let old = std::mem::replace(&mut self.components[id], new);
            if old == new {
                continue;
            }
            let (Some(old), Some(new)) = (old, new) else {
                return Err("component code became known or unknown");
            };
            for root in self.roots[id].iter() {
                self.code[root] =
                    self.code[root].map(|code| code.wrapping_sub(old).wrapping_add(new));
                affected.insert(root);
            }
            if self.ambient.contains(&id) {
                self.ambient_code =
                    self.ambient_code.map(|code| code.wrapping_sub(old).wrapping_add(new));
            }
        }
        if before_ambient != self.ambient_code {
            for root in 0..self.code.len() {
                affected.insert(root);
            }
        }
        let ambient = self.ambient_code.map(|code| vec![code]);
        let mut groups = FxHashSet::default();
        for root in affected.iter() {
            let alone = self.code[root].zip(ambient.as_ref()).map(|it| print_of(&it));
            if self.alone[root] != alone {
                self.alone[root] = alone;
                groups.insert(self.topology.groups[root]);
            }
        }
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!(
                "reach updated roots: {}, groups: {}; program={program}",
                affected.iter().count(),
                groups.len()
            );
        }
        refresh_groups(&self.groups, &self.alone, groups, &mut self.answer.0);
        self.answer.1 = ambient.as_ref().map(print_of);
        Ok(())
    }
}

fn dynamic_groups(written: &[usize], graph: &dynamic::Dynamic, count: usize) -> Vec<usize> {
    let mut groups: Vec<_> = (0..count).collect();
    fn find(groups: &mut [usize], mut at: usize) -> usize {
        while groups[at] != at {
            groups[at] = groups[groups[at]];
            at = groups[at];
        }
        at
    }
    for &node in written {
        let mask = &graph.masks[graph.owner[node]];
        let roots: Vec<_> = if mask.contains(count) {
            (0..count).collect()
        } else {
            mask.iter().filter(|&root| root < count).collect()
        };
        if let Some(&first) = roots.first() {
            for &root in &roots[1..] {
                let (a, b) = (find(&mut groups, first), find(&mut groups, root));
                groups[a.max(b)] = a.min(b);
            }
        }
    }
    (0..count).map(|root| find(&mut groups, root)).collect()
}

fn refresh_groups(
    members: &FxHashMap<usize, Vec<usize>>,
    alone: &[Option<u128>],
    changed: FxHashSet<usize>,
    reached: &mut [Reached],
) {
    for group in changed {
        let members = &members[&group];
        let mut together: Option<Vec<_>> = members.iter().map(|&root| alone[root]).collect();
        if let Some(prints) = &mut together {
            prints.sort_unstable();
        }
        for &root in members {
            reached[root].print = alone[root].zip(together.as_ref()).map(|it| print_of(&it));
        }
    }
}

#[salsa::tracked(returns(ref))]
fn reach_program(
    db: &dyn HirDatabase,
    input: ReachInput,
) -> (Vec<Reached>, Option<u128>, Vec<String>) {
    let topology = reach_topology(db, input);
    let alone: Vec<_> =
        (0..input.data(db).tests.len()).map(|id| reach_root_print(db, input, id)).collect();
    finish(topology, alone, reach_ambient(db, input).as_ref().map(print_of))
}

fn finish(topology: &Topology, alone: Vec<Option<u128>>, ambient: Option<u128>) -> Answer {
    let group = &topology.groups;
    // What one test of a group leaves in a static is what another finds: each has the
    // result it has for the code of all of them.
    let mut together: FxHashMap<usize, Option<Vec<u128>>> = FxHashMap::default();
    for (&group, &print) in std::iter::zip(group, &alone) {
        let prints = together.entry(group).or_insert_with(|| Some(Vec::new()));
        match (prints.as_mut(), print) {
            (Some(prints), Some(print)) => prints.push(print),
            _ => *prints = None,
        }
    }
    together.values_mut().flatten().for_each(|it| it.sort_unstable());
    let reached = std::iter::zip(group.iter().copied(), alone)
        .map(|(group, alone)| {
            let all = together[&group].as_ref();
            Reached { print: alone.zip(all).map(|it| print_of(&it)), group }
        })
        .collect();
    (reached, ambient, topology.graph.unknown.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edge_updates_split_static_groups_and_include_ambient_writes() {
        let roots = [(0, 0), (1, 1), (3, 2)];
        let mut graph = dynamic::Dynamic::new(
            vec![vec![2], vec![2], vec![], vec![]],
            vec![Some(1); 4],
            &roots,
            3,
        );
        assert_eq!(dynamic_groups(&[2], &graph, 2), vec![0, 0]);
        for (node, edges, expected) in [
            (0, vec![], vec![0, 1]),
            (3, vec![2], vec![0, 0]),
            (3, vec![], vec![0, 1]),
            (0, vec![2], vec![0, 0]),
        ] {
            let mut seeds = Vec::new();
            graph.change_edges(node, edges, &roots, &mut seeds);
            graph.settle(seeds);
            assert_eq!(dynamic_groups(&[2], &graph, 2), expected);
        }
        assert_eq!(dynamic_groups(&[], &graph, 2), vec![0, 1]);
    }

    #[test]
    fn refreshing_groups_matches_full_aggregation() {
        for mut alone in [Vec::new(), vec![Some(3), Some(5), Some(7)], vec![None, Some(5), Some(7)]]
        {
            let groups: Vec<_> =
                (0..alone.len()).map(|root| if root < 2 { 0 } else { 2 }).collect();
            let topology = Topology {
                graph: Graph::default(),
                components: Vec::new(),
                of: Vec::new(),
                tests: Vec::new(),
                ambient: Vec::new(),
                groups,
            };
            let mut members: FxHashMap<_, Vec<_>> = FxHashMap::default();
            for (root, &group) in topology.groups.iter().enumerate() {
                members.entry(group).or_default().push(root);
            }
            let mut reached = finish(&topology, alone.clone(), None).0;
            refresh_groups(&members, &alone, FxHashSet::default(), &mut reached);
            assert_eq!(reached, finish(&topology, alone.clone(), None).0);
            for value in [Some(11), None, Some(3)] {
                let Some(first) = alone.first_mut() else { continue };
                *first = value;
                refresh_groups(&members, &alone, [0].into_iter().collect(), &mut reached);
                assert_eq!(reached, finish(&topology, alone.clone(), None).0);
            }
        }
    }
}
