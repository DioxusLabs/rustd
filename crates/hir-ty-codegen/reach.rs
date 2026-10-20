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

use crate::next_solver::TyKind;

use crate::{db::HirDatabase, traits::StoredParamEnvAndCrate};

use super::{
    CodegenError, Instance, InstanceDef, compiled_instance, compiled_root, compiled_static,
    fragment::{DataRequest, FuncTarget, Requests},
    instance_serial, is_thread_local,
    patch::Mark,
    print_of, root_serial, static_serial,
};

#[derive(Clone, PartialEq, Eq, Hash)]
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

#[derive(Default)]
struct Graph {
    ids: FxHashMap<Node, usize>,
    /// The print of each node's own code and of the source locations it reports.
    own: Vec<Option<u128>>,
    edges: Vec<Vec<usize>>,
    /// The statics among the nodes that a running program can change.
    written: Vec<usize>,
    /// The crates an edit can change the code of.
    edited: FxHashSet<Crate>,
    /// The first nodes that did not compile, and why.
    unknown: Vec<String>,
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
        let first = self.own.len();
        let mut stack = vec![(first, self.add(db, node).into_iter())];
        while let Some((id, targets)) = stack.last_mut() {
            let id = *id;
            let Some(target) = targets.next() else {
                stack.pop();
                continue;
            };
            let known = self.ids.get(&target).copied();
            let target = known.unwrap_or_else(|| {
                let new = self.own.len();
                stack.push((new, self.add(db, target).into_iter()));
                new
            });
            self.edges[id].push(target);
        }
        first
    }

    /// Takes the node in and says what it refers to.
    fn add(&mut self, db: &dyn HirDatabase, node: Node) -> Vec<Node> {
        let id = self.own.len();
        self.ids.insert(node.clone(), id);
        self.edges.push(Vec::new());
        if self.settled(db, &node) || foreign(db, &node) {
            self.own.push(Some(0));
            return Vec::new();
        }
        let compiled: Result<(u128, &Requests), &CodegenError> = match &node {
            Node::Root(func) => {
                compiled_root(db, *func).as_ref().map(|it| (root_serial(db, *func), &it.requests))
            }
            Node::Instance(instance, env) => compiled_instance(db, instance.clone(), env.clone())
                .as_ref()
                .map(|it| (instance_serial(db, instance.clone(), env.clone()), &it.requests)),
            Node::Static(id) => {
                compiled_static(db, *id).as_ref().map(|it| (static_serial(db, *id), &it.requests))
            }
        };
        if let Node::Static(it) = node
            && (is_thread_local(db, it)
                || compiled_static(db, it).as_ref().map_or(true, |it| it.writable))
        {
            self.written.push(id);
        }
        let (serial, requests) = match compiled {
            Ok(compiled) => compiled,
            Err(why) => {
                // `TypeId::of` is a number the build takes from rustc, of the type alone.
                let known = matches!(&node, Node::Instance(it, _) if names_type_id(db, it));
                if !known && self.unknown.len() < 8 {
                    self.unknown.push(format!("{}: {why:?}", node.name(db)));
                }
                self.own.push(known.then_some(0));
                return Vec::new();
            }
        };
        self.own.push(Some(print_of(&Mark::new(db, serial, requests).seen())));
        let funcs = requests.funcs.iter().filter_map(|it| match &it.target {
            FuncTarget::Instance(instance, env) => Some(match instance.def {
                InstanceDef::Fn(func) if instance.args.as_ref().is_empty() => Node::Root(func),
                _ => Node::Instance(instance.clone(), env.clone()),
            }),
            // Code rustc compiled, which is the same until cargo builds again, or a name the
            // linker resolves, which the caller hands in as reached by everything.
            FuncTarget::Symbol(_) | FuncTarget::Path(_) | FuncTarget::Asm(_) => None,
        });
        let statics = requests.datas.iter().filter_map(|it| match it {
            DataRequest::Static(id) => Some(Node::Static(*id)),
            _ => None,
        });
        funcs.chain(statics).collect()
    }

    /// Whether the node is of a crate no edit reaches, and of nothing else: a function
    /// without type arguments, or a static. What it calls is then of such crates too,
    /// unless it was handed it when the program ran, by code that is a node of its own.
    fn settled(&self, db: &dyn HirDatabase, node: &Node) -> bool {
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
        !self.edited.contains(&krate)
    }
    /// The strongly connected components, each after the ones it refers to, and the
    /// component of each node.
    fn components(&self) -> (Vec<Vec<usize>>, Vec<usize>) {
        const NONE: usize = usize::MAX;
        let count = self.own.len();
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
#[derive(Clone, Default, PartialEq, Eq)]
struct Bits(Vec<u64>);

impl Bits {
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
pub fn reached(
    db: &dyn HirDatabase,
    edited: FxHashSet<Crate>,
    tests: &[FunctionId],
    always: &[FunctionId],
    kept: &[StaticId],
) -> (Vec<Reached>, Option<u128>, Vec<String>) {
    let mut graph = Graph { edited, ..Graph::default() };
    let tests: Vec<usize> = tests.iter().map(|&it| graph.node(db, Node::Root(it))).collect();
    let mut ambient: Vec<usize> = always.iter().map(|&it| graph.node(db, Node::Root(it))).collect();
    ambient.extend(kept.iter().map(|&it| graph.node(db, Node::Static(it))));
    let (components, of) = graph.components();
    let written: FxHashMap<usize, usize> =
        graph.written.iter().enumerate().map(|(at, &node)| (node, at)).collect();
    // Per component: the print of all it reaches, and the written statics among that.
    let mut prints: Vec<Option<u128>> = Vec::with_capacity(components.len());
    let mut shared: Vec<Bits> = Vec::with_capacity(components.len());
    for (at, members) in components.iter().enumerate() {
        let mut own: Option<Vec<u128>> = members.iter().map(|&it| graph.own[it]).collect();
        if let Some(own) = &mut own {
            own.sort_unstable();
        }
        let mut below: Vec<usize> =
            members.iter().flat_map(|&it| &graph.edges[it]).map(|&it| of[it]).collect();
        below.sort_unstable();
        below.dedup();
        below.retain(|&it| it != at);
        let mut statics = Bits::default();
        members.iter().filter_map(|it| written.get(it)).for_each(|&it| statics.insert(it));
        let mut reached: Option<Vec<u128>> = below.iter().map(|&it| prints[it]).collect();
        if let Some(reached) = &mut reached {
            reached.sort_unstable();
        }
        for &it in &below {
            statics.union(&shared[it]);
        }
        prints.push(own.zip(reached).map(|it| print_of(&it)));
        shared.push(statics);
    }
    let mut everywhere: Vec<Option<u128>> = ambient.iter().map(|&it| prints[of[it]]).collect();
    everywhere.sort_unstable();
    everywhere.dedup();
    let everywhere: Option<Vec<u128>> = everywhere.into_iter().collect();
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
    let alone: Vec<Option<u128>> = tests
        .iter()
        .map(|&it| prints[of[it]].zip(everywhere.as_ref()).map(|it| print_of(&it)))
        .collect();
    let group: Vec<usize> = (0..tests.len()).map(|at| find(&mut group, at)).collect();
    // What one test of a group leaves in a static is what another finds: each has the
    // result it has for the code of all of them.
    let mut together: FxHashMap<usize, Option<Vec<u128>>> = FxHashMap::default();
    for (&group, &print) in std::iter::zip(&group, &alone) {
        let prints = together.entry(group).or_insert_with(|| Some(Vec::new()));
        match (prints.as_mut(), print) {
            (Some(prints), Some(print)) => prints.push(print),
            _ => *prints = None,
        }
    }
    together.values_mut().flatten().for_each(|it| it.sort_unstable());
    let reached = std::iter::zip(group, alone)
        .map(|(group, alone)| {
            let all = together[&group].as_ref();
            Reached { print: alone.zip(all).map(|it| print_of(&it)), group }
        })
        .collect();
    (reached, everywhere.as_ref().map(print_of), graph.unknown)
}
