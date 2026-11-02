use rand::{Rng, SeedableRng, rngs::StdRng};
use reactive_graph::{
    computed::ArcMemo,
    prelude::{Get, GetUntracked, Set},
    signal::ArcRwSignal,
};
use rustc_hash::{FxHashMap, FxHashSet};
use salsa::{Database, Durability, Setter};
use std::{
    collections::{BTreeMap, VecDeque},
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    time::Instant,
};

#[derive(Clone, Debug, PartialEq, Eq, salsa::SalsaValue)]
struct FnSrc {
    sig: u64,
    body: u64,
    callees: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, salsa::SalsaValue)]
struct Model {
    crates: usize,
    files: usize,
    functions: usize,
    roots: Vec<usize>,
    dependencies: Vec<Vec<usize>>,
    signatures: Vec<Vec<usize>>,
}

impl Model {
    fn file(&self, node: usize) -> usize {
        node / self.functions
    }
    fn krate(&self, node: usize) -> usize {
        self.file(node) / self.files
    }
    fn count(&self) -> usize {
        self.crates * self.files * self.functions
    }
}

#[salsa::input]
struct FileText {
    #[returns(ref)]
    text: Vec<FnSrc>,
}

#[salsa::input]
struct Input {
    #[returns(ref)]
    files: Vec<FileText>,
    #[returns(ref)]
    model: Model,
}

type Counts = BTreeMap<salsa::IngredientIndex, (u64, u64)>;

#[salsa::db]
#[derive(Clone)]
struct Db {
    storage: salsa::Storage<Self>,
    counts: Arc<Mutex<Counts>>,
}

impl Default for Db {
    fn default() -> Self {
        let counts = Arc::new(Mutex::new(Counts::new()));
        let observed = counts.clone();
        Self {
            storage: salsa::Storage::new(Some(Box::new(move |event| {
                let (key, executed) = match event.kind {
                    salsa::EventKind::WillExecute { database_key } => (database_key, true),
                    salsa::EventKind::DidValidateMemoizedValue { database_key } => {
                        (database_key, false)
                    }
                    _ => return,
                };
                let mut counts = observed.lock().unwrap();
                let count = counts.entry(key.ingredient_index()).or_default();
                if executed {
                    count.0 += 1;
                } else {
                    count.1 += 1;
                }
            }))),
            counts,
        }
    }
}

#[salsa::db]
impl salsa::Database for Db {}

fn mix(a: u64, b: u64) -> u64 {
    (a ^ b.wrapping_add(0x9e3779b97f4a7c15)).rotate_left(17).wrapping_mul(0xbf58476d1ce4e5b9)
}

fn fold(values: impl IntoIterator<Item = u64>) -> u64 {
    values.into_iter().fold(0, mix)
}

#[salsa::tracked(returns(ref))]
fn item_tree(db: &dyn Database, file: FileText) -> Vec<u64> {
    file.text(db).iter().map(|f| f.sig).collect()
}

#[salsa::tracked(returns(copy))]
fn def_map(db: &dyn Database, input: Input, krate: usize) -> u64 {
    let model = input.model(db);
    fold(
        (krate * model.files..(krate + 1) * model.files)
            .map(|file| fold(item_tree(db, input.files(db)[file]).iter().copied()))
            .chain(model.dependencies[krate].iter().map(|&dep| def_map(db, input, dep))),
    )
}

#[salsa::tracked(returns(ref))]
fn body(db: &dyn Database, input: Input, node: usize) -> (u64, Vec<usize>) {
    let model = input.model(db);
    let source = &input.files(db)[model.file(node)].text(db)[node % model.functions];
    (source.body, source.callees.clone())
}

#[salsa::tracked(returns(copy))]
fn infer(db: &dyn Database, input: Input, node: usize) -> u64 {
    let model = input.model(db);
    let (value, callees) = body(db, input, node);
    let mut hash = mix(*value, def_map(db, input, model.krate(node)));
    for &dep in callees.iter().chain(&model.signatures[node]) {
        hash = mix(hash, item_tree(db, input.files(db)[model.file(dep)])[dep % model.functions]);
    }
    for i in 0..16 {
        hash = mix(hash, i);
    }
    hash
}

#[salsa::tracked(returns(copy))]
fn mir(db: &dyn Database, input: Input, node: usize) -> u64 {
    mix(infer(db, input, node), 37)
}

#[salsa::tracked(returns(ref))]
fn codegen(db: &dyn Database, input: Input, node: usize) -> (u64, Vec<usize>) {
    (mix(mir(db, input, node), 91), body(db, input, node).1.clone())
}

#[salsa::tracked(returns(ref))]
fn reach_edges(db: &dyn Database, input: Input, node: usize) -> Vec<usize> {
    codegen(db, input, node).1.clone()
}

#[salsa::tracked(returns(copy))]
fn reach_own(db: &dyn Database, input: Input, node: usize) -> u64 {
    codegen(db, input, node).0
}

#[salsa::interned]
struct Component<'db> {
    #[returns(ref)]
    members: Vec<usize>,
    #[returns(ref)]
    below: Vec<Component<'db>>,
}

struct Tarjan {
    indices: Vec<Option<usize>>,
    low: Vec<usize>,
    stack: Vec<usize>,
    active: Vec<bool>,
    next: usize,
    groups: Vec<Vec<usize>>,
}

impl Tarjan {
    fn visit(&mut self, node: usize, edges: &[Vec<usize>]) {
        self.indices[node] = Some(self.next);
        self.low[node] = self.next;
        self.next += 1;
        self.stack.push(node);
        self.active[node] = true;
        for &to in &edges[node] {
            if self.indices[to].is_none() {
                self.visit(to, edges);
                self.low[node] = self.low[node].min(self.low[to]);
            } else if self.active[to] {
                self.low[node] = self.low[node].min(self.indices[to].unwrap());
            }
        }
        if self.low[node] == self.indices[node].unwrap() {
            let mut group = Vec::new();
            loop {
                let member = self.stack.pop().unwrap();
                self.active[member] = false;
                group.push(member);
                if member == node {
                    break;
                }
            }
            group.sort_unstable();
            self.groups.push(group);
        }
    }
}

#[salsa::tracked(returns(ref))]
fn reach_topology<'db>(db: &'db dyn Database, input: Input) -> Vec<Component<'db>> {
    let model = input.model(db);
    let n = model.count();
    let mut edges = vec![Vec::new(); n];
    let mut seen = vec![false; n];
    let mut pending = model.roots.clone();
    while let Some(node) = pending.pop() {
        if std::mem::replace(&mut seen[node], true) {
            continue;
        }
        edges[node] = reach_edges(db, input, node).clone();
        pending.extend(&edges[node]);
    }
    let mut tarjan = Tarjan {
        indices: vec![None; n],
        low: vec![0; n],
        stack: Vec::new(),
        active: vec![false; n],
        next: 0,
        groups: Vec::new(),
    };
    for &root in &model.roots {
        if tarjan.indices[root].is_none() {
            tarjan.visit(root, &edges);
        }
    }
    let mut owners = vec![None; n];
    for group in tarjan.groups {
        let mut below: Vec<_> =
            group.iter().flat_map(|&node| &edges[node]).filter_map(|&to| owners[to]).collect();
        let mut unique = FxHashSet::default();
        below.retain(|&c| unique.insert(c));
        let component = Component::new(db, group.clone(), below);
        for node in group {
            owners[node] = Some(component);
        }
    }
    model.roots.iter().map(|&root| owners[root].unwrap()).collect()
}

#[salsa::tracked(returns(copy))]
fn reach_component_print<'db>(
    db: &'db dyn Database,
    input: Input,
    component: Component<'db>,
) -> u64 {
    component.members(db).iter().map(|&node| reach_own(db, input, node)).fold(0, u64::wrapping_add)
}

#[salsa::tracked(returns(copy))]
fn reach_root_print(db: &dyn Database, input: Input, root: usize) -> u64 {
    let mut seen = FxHashSet::default();
    let mut pending = vec![reach_topology(db, input)[root]];
    let mut sum = 0u64;
    while let Some(component) = pending.pop() {
        if seen.insert(component) {
            sum = sum.wrapping_add(reach_component_print(db, input, component));
            pending.extend(component.below(db));
        }
    }
    sum
}

#[salsa::tracked(returns(ref))]
fn reach_program(db: &dyn Database, input: Input) -> Vec<u64> {
    (0..input.model(db).roots.len()).map(|i| reach_root_print(db, input, i)).collect()
}

fn reference(model: &Model, sources: &[Vec<FnSrc>]) -> Vec<u64> {
    let sig = |node| sources[model.file(node)][node % model.functions].sig;
    let mut maps = Vec::new();
    for krate in 0..model.crates {
        maps.push(fold(
            (krate * model.files..(krate + 1) * model.files)
                .map(|file| fold(sources[file].iter().map(|f| f.sig)))
                .chain(model.dependencies[krate].iter().map(|&dep| maps[dep])),
        ));
    }
    let codes: Vec<_> = (0..model.count())
        .map(|node| {
            let source = &sources[model.file(node)][node % model.functions];
            let mut hash = mix(source.body, maps[model.krate(node)]);
            for &dep in source.callees.iter().chain(&model.signatures[node]) {
                hash = mix(hash, sig(dep));
            }
            for i in 0..16 {
                hash = mix(hash, i);
            }
            mix(mix(hash, 37), 91)
        })
        .collect();
    model
        .roots
        .iter()
        .map(|&root| {
            let mut seen = vec![false; model.count()];
            let mut pending = vec![root];
            let mut sum = 0u64;
            while let Some(node) = pending.pop() {
                if std::mem::replace(&mut seen[node], true) {
                    continue;
                }
                sum = sum.wrapping_add(codes[node]);
                pending.extend(&sources[model.file(node)][node % model.functions].callees);
            }
            sum
        })
        .collect()
}

#[derive(Default)]
struct PushTiming {
    salsa_ms: f64,
    rebuild_ms: f64,
    calls: usize,
    fallback: bool,
    rebuilt: bool,
    merges: usize,
    splits: usize,
    split_checks: usize,
    own_changes: Vec<(usize, u64)>,
}

struct Push {
    edges: Vec<Vec<usize>>,
    reverse: Vec<Vec<usize>>,
    own: Vec<Option<u64>>,
    trees: Vec<Vec<u64>>,
    owner: Vec<usize>,
    members: Vec<Vec<usize>>,
    below: Vec<Vec<usize>>,
    above: Vec<Vec<usize>>,
    component_prints: Vec<u64>,
    roots_at: Vec<Vec<usize>>,
    prints: Vec<u64>,
    masks: Vec<Vec<u64>>,
    free: Vec<usize>,
    track_roots: bool,
}

impl Push {
    fn cold(db: &dyn Database, input: Input) -> Self {
        Self::cold_layer(db, input, true)
    }

    fn cold_layer(db: &dyn Database, input: Input, track_roots: bool) -> Self {
        let n = input.model(db).count();
        let mut graph = Self {
            edges: vec![Vec::new(); n],
            reverse: vec![Vec::new(); n],
            own: vec![None; n],
            trees: input.files(db).iter().map(|&file| item_tree(db, file).clone()).collect(),
            owner: vec![usize::MAX; n],
            members: Vec::new(),
            below: Vec::new(),
            above: Vec::new(),
            component_prints: Vec::new(),
            roots_at: Vec::new(),
            prints: Vec::new(),
            masks: Vec::new(),
            free: Vec::new(),
            track_roots,
        };
        let mut pending = input.model(db).roots.clone();
        let mut timing = PushTiming::default();
        while let Some(node) = pending.pop() {
            if graph.own[node].is_some() {
                continue;
            }
            let (own, edges) = Self::pull(db, input, node, &mut timing);
            graph.own[node] = Some(own);
            pending.extend(&edges);
            graph.edges[node] = edges;
        }
        graph.rebuild(&input.model(db).roots);
        graph
    }

    fn pull(
        db: &dyn Database,
        input: Input,
        node: usize,
        timing: &mut PushTiming,
    ) -> (u64, Vec<usize>) {
        let began = Instant::now();
        let result = codegen(db, input, node);
        timing.salsa_ms += began.elapsed().as_secs_f64() * 1000.;
        timing.calls += 1;
        result.clone()
    }

    fn rebuild(&mut self, roots: &[usize]) {
        let n = self.own.len();
        self.reverse = vec![Vec::new(); n];
        for (node, edges) in self.edges.iter().enumerate() {
            for &to in edges {
                self.reverse[to].push(node);
            }
        }
        let mut tarjan = Tarjan {
            indices: vec![None; n],
            low: vec![0; n],
            stack: Vec::new(),
            active: vec![false; n],
            next: 0,
            groups: Vec::new(),
        };
        for &root in roots {
            if tarjan.indices[root].is_none() {
                tarjan.visit(root, &self.edges);
            }
        }
        self.members = tarjan.groups;
        self.owner.fill(usize::MAX);
        for (component, members) in self.members.iter().enumerate() {
            for &node in members {
                self.owner[node] = component;
            }
        }
        let count = self.members.len();
        self.below = vec![Vec::new(); count];
        self.above = vec![Vec::new(); count];
        self.component_prints = vec![0; count];
        self.roots_at = vec![Vec::new(); count];
        for (component, members) in self.members.iter().enumerate() {
            let mut below = Vec::new();
            for &node in members {
                self.component_prints[component] =
                    self.component_prints[component].wrapping_add(self.own[node].unwrap());
                below.extend(
                    self.edges[node].iter().map(|&to| self.owner[to]).filter(|&to| to != component),
                );
            }
            below.sort_unstable();
            below.dedup();
            for &to in &below {
                self.above[to].push(component);
            }
            self.below[component] = below;
        }
        self.prints = vec![0; roots.len()];
        self.masks =
            vec![vec![0; if self.track_roots { roots.len().div_ceil(64) } else { 0 }]; count];
        self.free.clear();
        for (root, &node) in roots.iter().enumerate() {
            let component = self.owner[node];
            self.roots_at[component].push(root);
            if !self.track_roots {
                continue;
            }
            let mut pending = vec![component];
            let mut seen = vec![false; count];
            while let Some(component) = pending.pop() {
                if std::mem::replace(&mut seen[component], true) {
                    continue;
                }
                self.prints[root] =
                    self.prints[root].wrapping_add(self.component_prints[component]);
                self.masks[component][root / 64] |= 1 << (root % 64);
                pending.extend(&self.below[component]);
            }
        }
    }

    fn adjust_prints(&mut self, component: usize, delta: u64) {
        for (word, &mask) in self.masks[component].iter().enumerate() {
            let mut bits = mask;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                let root = word * 64 + bit;
                self.prints[root] = self.prints[root].wrapping_add(delta);
                bits &= bits - 1;
            }
        }
    }

    fn add_component(&mut self, members: Vec<usize>) -> usize {
        let component = self.free.pop().unwrap_or(self.members.len());
        let mut print = 0u64;
        for &node in &members {
            self.owner[node] = component;
            print = print.wrapping_add(self.own[node].unwrap());
        }
        if component < self.members.len() {
            self.members[component] = members;
            self.component_prints[component] = print;
            return component;
        }
        self.members.push(members);
        self.component_prints.push(print);
        self.below.push(Vec::new());
        self.above.push(Vec::new());
        self.roots_at.push(Vec::new());
        self.masks.push(vec![0; if self.track_roots { self.prints.len().div_ceil(64) } else { 0 }]);
        component
    }

    fn repair(&mut self, sources: &[usize], seeds: &mut Vec<usize>) {
        for &component in sources {
            let old = std::mem::take(&mut self.below[component]);
            let mut below = Vec::new();
            for &node in &self.members[component] {
                below.extend(self.edges[node].iter().map(|&to| self.owner[to]));
            }
            below.retain(|&to| to != component);
            below.sort_unstable();
            below.dedup();
            for &to in &old {
                self.above[to].retain(|&from| from != component);
            }
            for &to in &below {
                self.above[to].push(component);
            }
            seeds.push(component);
            seeds.extend(old);
            seeds.extend(&below);
            self.below[component] = below;
        }
    }

    fn repartition(
        &mut self,
        old: &[usize],
        groups: Vec<Vec<usize>>,
        roots: &[usize],
        seeds: &mut Vec<usize>,
    ) {
        let mut sources = old.to_vec();
        let mut root_ids = Vec::new();
        for &component in old {
            sources.extend(&self.above[component]);
            root_ids.append(&mut self.roots_at[component]);
            self.adjust_prints(component, 0u64.wrapping_sub(self.component_prints[component]));
            self.masks[component].fill(0);
            self.component_prints[component] = 0;
            self.members[component].clear();
        }
        for members in groups {
            sources.push(self.add_component(members));
        }
        for root in root_ids {
            self.roots_at[self.owner[roots[root]]].push(root);
        }
        sources.sort_unstable();
        sources.dedup();
        self.repair(&sources, seeds);
        self.free.extend(old);
    }

    fn closure(start: usize, edges: &[Vec<usize>]) -> FxHashSet<usize> {
        let mut seen = FxHashSet::default();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if seen.insert(node) {
                pending.extend(&edges[node]);
            }
        }
        seen
    }

    fn split(&mut self, component: usize, roots: &[usize], seeds: &mut Vec<usize>) -> bool {
        let members = &self.members[component];
        let local: FxHashMap<_, _> =
            members.iter().enumerate().map(|(i, &node)| (node, i)).collect();
        let edges: Vec<Vec<_>> = members
            .iter()
            .map(|&node| self.edges[node].iter().filter_map(|to| local.get(to).copied()).collect())
            .collect();
        let n = members.len();
        let mut tarjan = Tarjan {
            indices: vec![None; n],
            low: vec![0; n],
            stack: Vec::new(),
            active: vec![false; n],
            next: 0,
            groups: Vec::new(),
        };
        for node in 0..n {
            if tarjan.indices[node].is_none() {
                tarjan.visit(node, &edges);
            }
        }
        if tarjan.groups.len() == 1 {
            return false;
        }
        let groups = tarjan
            .groups
            .into_iter()
            .map(|group| group.into_iter().map(|i| members[i]).collect())
            .collect();
        self.repartition(&[component], groups, roots, seeds);
        true
    }

    fn propagate(&mut self, seeds: Vec<usize>) {
        let mut queued = vec![false; self.members.len()];
        let mut pending = VecDeque::new();
        for component in seeds {
            if !std::mem::replace(&mut queued[component], true) {
                pending.push_back(component);
            }
        }
        while let Some(component) = pending.pop_front() {
            queued[component] = false;
            let mut mask = vec![0; self.prints.len().div_ceil(64)];
            for &root in &self.roots_at[component] {
                mask[root / 64] |= 1 << (root % 64);
            }
            for &from in &self.above[component] {
                for (word, &bits) in mask.iter_mut().zip(&self.masks[from]) {
                    *word |= bits;
                }
            }
            if mask == self.masks[component] {
                continue;
            }
            let print = self.component_prints[component];
            for (word, (&new, &old)) in mask.iter().zip(&self.masks[component]).enumerate() {
                let mut changed = new ^ old;
                while changed != 0 {
                    let bit = changed.trailing_zeros() as usize;
                    let delta =
                        if new & (1 << bit) != 0 { print } else { 0u64.wrapping_sub(print) };
                    let root = word * 64 + bit;
                    self.prints[root] = self.prints[root].wrapping_add(delta);
                    changed &= changed - 1;
                }
            }
            self.masks[component] = mask;
            for &to in &self.below[component] {
                if !std::mem::replace(&mut queued[to], true) {
                    pending.push_back(to);
                }
            }
        }
    }

    fn change_edges(
        &mut self,
        node: usize,
        edges: Vec<usize>,
        roots: &[usize],
        seeds: &mut Vec<usize>,
        timing: &mut PushTiming,
    ) {
        let old = self.edges[node].clone();
        for to in old.iter().copied().filter(|to| !edges.contains(to)) {
            let from = self.owner[node];
            let target = self.owner[to];
            self.edges[node].retain(|&edge| edge != to);
            self.reverse[to].retain(|&source| source != node);
            if from == target {
                timing.split_checks += 1;
                timing.splits += usize::from(self.split(from, roots, seeds));
            } else {
                self.repair(&[from], seeds);
            }
        }
        for to in edges.iter().copied().filter(|to| !old.contains(to)) {
            self.edges[node].push(to);
            self.reverse[to].push(node);
            let from = self.owner[node];
            let target = self.owner[to];
            if from == target {
                continue;
            }
            let forward = Self::closure(target, &self.below);
            if forward.contains(&from) {
                let backward = Self::closure(from, &self.above);
                let merged: Vec<_> = forward.intersection(&backward).copied().collect();
                let members =
                    merged.iter().flat_map(|&id| self.members[id].iter().copied()).collect();
                self.repartition(&merged, vec![members], roots, seeds);
                timing.merges += 1;
            } else {
                self.repair(&[from], seeds);
            }
        }
        self.edges[node] = edges;
    }

    fn update(
        &mut self,
        db: &dyn Database,
        input: Input,
        edited: &[usize],
        signal: &str,
        topology: &str,
    ) -> PushTiming {
        let mut timing = PushTiming::default();
        let mut all = signal == "all";
        if !all {
            for &file in edited {
                let began = Instant::now();
                let tree = item_tree(db, input.files(db)[file]);
                timing.salsa_ms += began.elapsed().as_secs_f64() * 1000.;
                if self.trees[file] != *tree {
                    all = true;
                    timing.fallback = true;
                    self.trees[file] = tree.clone();
                }
            }
        }
        let model = input.model(db);
        let mut pending: Vec<_> = if all {
            self.own
                .iter()
                .enumerate()
                .filter_map(|(node, own)| own.is_some().then_some(node))
                .collect()
        } else {
            edited
                .iter()
                .flat_map(|&file| file * model.functions..(file + 1) * model.functions)
                .collect()
        };
        let mut pulled = vec![false; self.own.len()];
        let mut changes = Vec::new();
        let mut new_nodes = Vec::new();
        while let Some(node) = pending.pop() {
            if std::mem::replace(&mut pulled[node], true) {
                continue;
            }
            let (own, edges) = Self::pull(db, input, node, &mut timing);
            if self.own[node].is_none() || self.edges[node] != edges {
                timing.rebuilt = true;
                pending.extend(edges.iter().copied().filter(|&to| self.own[to].is_none()));
                changes.push((node, edges));
            }
            if let Some(old) = self.own[node] {
                let component = self.owner[node];
                if component != usize::MAX {
                    let delta = own.wrapping_sub(old);
                    if delta != 0 {
                        self.component_prints[component] =
                            self.component_prints[component].wrapping_add(delta);
                        if self.track_roots {
                            self.adjust_prints(component, delta);
                        }
                    }
                }
            } else {
                new_nodes.push(node);
            }
            if !self.track_roots && self.own[node] != Some(own) {
                timing.own_changes.push((node, own));
            }
            self.own[node] = Some(own);
        }
        if timing.rebuilt {
            let began = Instant::now();
            if topology == "full" {
                for (node, edges) in changes {
                    self.edges[node] = edges;
                }
                self.rebuild(&model.roots);
            } else {
                let mut seeds = Vec::new();
                for node in new_nodes {
                    seeds.push(self.add_component(vec![node]));
                }
                for (node, edges) in changes {
                    self.change_edges(node, edges, &model.roots, &mut seeds, &mut timing);
                }
                if self.track_roots {
                    self.propagate(seeds);
                }
            }
            timing.rebuild_ms = began.elapsed().as_secs_f64() * 1000.;
        }
        timing
    }

    fn bytes(&self) -> usize {
        fn nested<T>(vectors: &Vec<Vec<T>>) -> usize {
            vectors.capacity() * size_of::<Vec<T>>()
                + vectors.iter().map(|v| v.capacity() * size_of::<T>()).sum::<usize>()
        }
        size_of::<Self>()
            + nested(&self.edges)
            + nested(&self.reverse)
            + nested(&self.trees)
            + nested(&self.members)
            + nested(&self.below)
            + nested(&self.above)
            + nested(&self.roots_at)
            + nested(&self.masks)
            + self.own.capacity() * size_of::<Option<u64>>()
            + self.owner.capacity() * size_of::<usize>()
            + self.component_prints.capacity() * size_of::<u64>()
            + self.prints.capacity() * size_of::<u64>()
            + self.free.capacity() * size_of::<usize>()
    }
}

#[derive(Clone, Default, PartialEq)]
struct Contributions {
    values: im::HashMap<usize, u64>,
    print: u64,
}

struct Reactive {
    signals: Vec<ArcRwSignal<u64>>,
    components: Vec<Option<ArcMemo<Contributions>>>,
    roots: Vec<ArcMemo<u64>>,
    component_runs: Arc<AtomicUsize>,
    root_runs: Arc<AtomicUsize>,
}

impl Reactive {
    fn cold(graph: &Push, roots: &[usize]) -> Self {
        let mut layer = Self {
            signals: graph.own.iter().map(|own| ArcRwSignal::new(own.unwrap_or(0))).collect(),
            components: Vec::new(),
            roots: Vec::new(),
            component_runs: Arc::default(),
            root_runs: Arc::default(),
        };
        layer.rebuild(graph, roots);
        layer
    }

    fn component(&mut self, id: usize, graph: &Push) -> ArcMemo<Contributions> {
        if let Some(memo) = &self.components[id] {
            return memo.clone();
        }
        let children: Vec<_> =
            graph.below[id].iter().map(|&to| self.component(to, graph)).collect();
        let members: Vec<_> =
            graph.members[id].iter().map(|&node| self.signals[node].clone()).collect();
        let runs = self.component_runs.clone();
        let memo = ArcMemo::new(move |_| {
            runs.fetch_add(1, Ordering::Relaxed);
            let mut values: Vec<_> = children.iter().map(Get::get).collect();
            let mut result = values
                .iter()
                .enumerate()
                .max_by_key(|(_, value)| value.values.len())
                .map(|(index, _)| index)
                .map_or_else(Contributions::default, |index| values.swap_remove(index));
            for child in values {
                for (&key, &value) in &child.values {
                    if !result.values.contains_key(&key) {
                        result.values.insert(key, value);
                        result.print = result.print.wrapping_add(value);
                    }
                }
            }
            let own = members.iter().fold(0u64, |sum, signal| sum.wrapping_add(signal.get()));
            result.values.insert(id, own);
            result.print = result.print.wrapping_add(own);
            result
        });
        memo.get_untracked();
        self.components[id] = Some(memo.clone());
        memo
    }

    fn rebuild(&mut self, graph: &Push, roots: &[usize]) {
        self.clear();
        self.components = vec![None; graph.members.len()];
        for id in 0..graph.members.len() {
            if !graph.members[id].is_empty() {
                self.component(id, graph);
            }
        }
        self.roots = roots
            .iter()
            .map(|&node| {
                let component = self.components[graph.owner[node]].as_ref().unwrap().clone();
                let runs = self.root_runs.clone();
                ArcMemo::new(move |_| {
                    runs.fetch_add(1, Ordering::Relaxed);
                    component.get().print
                })
            })
            .collect();
    }

    fn clear(&mut self) {
        self.roots.clear();
        self.components.clear();
    }

    fn reset_counts(&self) {
        self.component_runs.store(0, Ordering::Relaxed);
        self.root_runs.store(0, Ordering::Relaxed);
    }

    fn counts(&self) -> (usize, usize) {
        (self.component_runs.load(Ordering::Relaxed), self.root_runs.load(Ordering::Relaxed))
    }

    fn pull(&self) -> Vec<u64> {
        self.roots.iter().map(GetUntracked::get_untracked).collect()
    }

    fn update(
        &mut self,
        graph: &mut Push,
        db: &dyn Database,
        input: Input,
        edited: &[usize],
        signal: &str,
        topology: &str,
    ) -> (Vec<u64>, PushTiming) {
        self.reset_counts();
        let mut timing = graph.update(db, input, edited, signal, topology);
        let began = Instant::now();
        if timing.rebuilt {
            self.clear();
        }
        for &(node, own) in &timing.own_changes {
            self.signals[node].set(own);
        }
        if timing.rebuilt {
            self.rebuild(graph, &input.model(db).roots);
        }
        let prints = self.pull();
        if timing.rebuilt {
            timing.rebuild_ms += began.elapsed().as_secs_f64() * 1000.;
        }
        (prints, timing)
    }
}

struct Options {
    scale: String,
    variant: String,
    signal: String,
    topology: String,
    edit: String,
    crates: usize,
    files: usize,
    functions: usize,
    roots: usize,
    hot_crates: usize,
    callees: usize,
    fanin: usize,
    edits: usize,
    seed: u64,
}

impl Options {
    fn parse() -> Self {
        let args: Vec<_> = std::env::args().skip(1).collect();
        if args.iter().any(|a| a == "--help") {
            println!(
                "reach-incr --variant salsa|salsa-tiers|push|push-low|reactive --signal all|edit --topology incremental|full --edit all|leaf|edge|edge-cycle|sig --scale small|mid|codex [--crates K --files N --fns N --roots N --hot-crates N --callees N --fanin N --edits N --seed N]"
            );
            std::process::exit(0);
        }
        assert!(args.len() % 2 == 0, "options require values; see --help");
        let flags: FxHashMap<_, _> =
            args.as_chunks::<2>().0.iter().map(|p| (p[0].as_str(), p[1].as_str())).collect();
        for flag in flags.keys() {
            assert!(
                [
                    "--variant",
                    "--signal",
                    "--topology",
                    "--edit",
                    "--scale",
                    "--crates",
                    "--files",
                    "--fns",
                    "--roots",
                    "--hot-crates",
                    "--callees",
                    "--fanin",
                    "--edits",
                    "--seed"
                ]
                .contains(flag),
                "unknown flag {flag}"
            );
        }
        let scale = *flags.get("--scale").unwrap_or(&"small");
        let (crates, files, functions, roots) = match scale {
            "small" => (20, 5, 50, 50),
            "mid" => (60, 10, 50, 200),
            "codex" => (100, 12, 100, 731),
            _ => panic!("unknown scale {scale}"),
        };
        let number = |name, default| {
            flags.get(name).map_or(default, |v| v.parse::<usize>().expect("invalid integer"))
        };
        let variant = flags.get("--variant").unwrap_or(&"salsa").to_string();
        assert!(
            matches!(variant.as_str(), "salsa" | "salsa-tiers" | "push" | "push-low" | "reactive"),
            "unknown variant"
        );
        let signal = flags.get("--signal").unwrap_or(&"all").to_string();
        assert!(matches!(signal.as_str(), "all" | "edit"), "unknown signal");
        let topology = flags.get("--topology").unwrap_or(&"incremental").to_string();
        assert!(matches!(topology.as_str(), "incremental" | "full"), "unknown topology");
        let edit = flags.get("--edit").unwrap_or(&"all").to_string();
        assert!(
            matches!(edit.as_str(), "all" | "leaf" | "edge" | "edge-cycle" | "sig"),
            "unknown edit"
        );
        let result = Self {
            scale: scale.to_owned(),
            variant,
            signal,
            topology,
            edit,
            crates: number("--crates", crates),
            files: number("--files", files),
            functions: number("--fns", functions),
            roots: number("--roots", roots),
            hot_crates: number("--hot-crates", 1),
            callees: number("--callees", 5),
            fanin: number("--fanin", 20),
            edits: number("--edits", 20),
            seed: flags.get("--seed").map_or(42, |s| s.parse().expect("invalid seed")),
        };
        assert!(
            result.crates > 0
                && result.files > 0
                && result.functions > 0
                && result.roots > 0
                && result.edits > 1
        );
        assert!(result.hot_crates > 0 && result.hot_crates <= result.crates);
        assert!(result.roots <= result.hot_crates * result.files * result.functions);
        result
    }
}

fn generate(options: &Options) -> (Model, Vec<Vec<FnSrc>>) {
    let mut rng = StdRng::seed_from_u64(options.seed);
    let per_crate = options.files * options.functions;
    let count = options.crates * per_crate;
    let hot_start = count - options.hot_crates * per_crate;
    let mut model = Model {
        crates: options.crates,
        files: options.files,
        functions: options.functions,
        roots: (0..options.roots)
            .map(|i| hot_start + i * (count - hot_start) / options.roots)
            .collect(),
        dependencies: vec![Vec::new(); options.crates],
        signatures: vec![Vec::new(); count],
    };
    for krate in 1..options.crates {
        model.dependencies[krate].push(krate - 1);
        if krate > 2 {
            model.dependencies[krate].push(rng.random_range(0..krate - 1));
        }
    }
    let mut sources = vec![Vec::new(); options.crates * options.files];
    for node in 0..count {
        let krate = model.krate(node);
        let target = |rng: &mut StdRng| {
            if krate > 0 && rng.random_range(0..5) == 0 {
                let dep =
                    model.dependencies[krate][rng.random_range(0..model.dependencies[krate].len())];
                dep * per_crate + rng.random_range(0..per_crate)
            } else {
                krate * per_crate + rng.random_range(0..per_crate)
            }
        };
        let cluster_start = krate * per_crate + (node % per_crate / 44) * 44;
        let cluster_end = (cluster_start + 44).min((krate + 1) * per_crate);
        let mut callees: Vec<_> = (0..options.callees)
            .map(|i| {
                if i < 2 {
                    rng.random_range(cluster_start..cluster_end)
                } else if krate > 0 && rng.random_range(0..4) == 0 {
                    let dep = model.dependencies[krate]
                        [rng.random_range(0..model.dependencies[krate].len())];
                    dep * per_crate + rng.random_range(0..per_crate)
                } else {
                    rng.random_range(krate * per_crate..cluster_end)
                }
            })
            .collect();
        callees.sort_unstable();
        callees.dedup();
        let signatures = (0..options.fanin).map(|_| target(&mut rng)).collect();
        model.signatures[node] = signatures;
        sources[model.file(node)].push(FnSrc { sig: rng.random(), body: rng.random(), callees });
    }
    (model, sources)
}

fn rss() -> usize {
    std::fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmRSS:")
                .map(|v| v.split_whitespace().next().unwrap().parse().unwrap())
        })
        .unwrap()
}

fn quantile(values: &mut [f64], fraction: f64) -> f64 {
    values.sort_by(f64::total_cmp);
    if fraction == 0.5 && values.len().is_multiple_of(2) {
        return (values[values.len() / 2 - 1] + values[values.len() / 2]) / 2.;
    }
    values[((values.len() as f64 * fraction).ceil() as usize).saturating_sub(1)]
}

fn run(options: &Options, kind: &str) {
    let (model, mut sources) = generate(options);
    let node = model.roots[0];
    let file = model.file(node);
    let source = &sources[file][node % model.functions];
    let extra = if kind == "edge-cycle" {
        let edges: Vec<_> = sources.iter().flatten().map(|source| source.callees.clone()).collect();
        let mut reverse = vec![Vec::new(); model.count()];
        for (from, edges) in edges.iter().enumerate() {
            for &to in edges {
                reverse[to].push(from);
            }
        }
        let forward = Push::closure(node, &edges);
        let backward = Push::closure(node, &reverse);
        (0..model.count())
            .find(|to| backward.contains(to) && !forward.contains(to))
            .expect("no cycle-forming edge in this model")
    } else {
        (0..model.count()).find(|to| !source.callees.contains(to)).expect("no unused edge")
    };
    let mut db = Db::default();
    let durability = if matches!(options.variant.as_str(), "salsa-tiers" | "push" | "reactive") {
        Durability::MEDIUM
    } else {
        Durability::LOW
    };
    let files: Vec<_> = sources
        .iter()
        .map(|text| FileText::builder(text.clone()).text_durability(durability).new(&db))
        .collect();
    let input = Input::builder(files.clone(), model.clone()).durability(Durability::HIGH).new(&db);
    let began = Instant::now();
    let mut push = if options.variant == "reactive" {
        Some(Push::cold_layer(&db, input, false))
    } else {
        options.variant.starts_with("push").then(|| Push::cold(&db, input))
    };
    let before_reactive = rss();
    let mut reactive = (options.variant == "reactive")
        .then(|| Reactive::cold(push.as_ref().unwrap(), &model.roots));
    let cold = if let Some(layer) = &reactive {
        layer.pull()
    } else {
        match &push {
            Some(graph) => graph.prints.clone(),
            None => reach_program(&db, input).clone(),
        }
    };
    let cold_ms = began.elapsed().as_secs_f64() * 1000.;
    let cold_rss = rss();
    let reactive_rss =
        if reactive.is_some() { cold_rss.saturating_sub(before_reactive) } else { 0 };
    let mut peak_rss = cold_rss;
    if let Some(layer) = &reactive {
        let (component_runs, root_runs) = layer.counts();
        eprintln!(
            "memos cold {} {kind}: components={} roots={} component_runs={component_runs} root_runs={root_runs} reactive_rss_delta_kib={reactive_rss}",
            options.scale,
            layer.components.iter().flatten().count(),
            layer.roots.len()
        );
    }
    assert_eq!(cold, reference(&model, &sources), "cold mismatch");
    eprintln!(
        "cold {} {} {kind}: total={cold_ms:.3} ms rss_kib={cold_rss}; correctness: cold matched",
        options.variant, options.scale
    );
    if reactive.is_some() && (cold_ms > 60_000. || cold_rss > 1_048_576) {
        eprintln!(
            "RESOURCE STOP: reactive cold exceeded 60000 ms or 1048576 KiB; no warm edits attempted"
        );
        std::process::exit(2);
    }
    let mut rng = StdRng::seed_from_u64(options.seed + 1);
    let mut times = Vec::new();
    let mut totals = Vec::new();
    let mut ingredients = Counts::new();
    let mut salsa_times = Vec::new();
    let mut layer_times = Vec::new();
    let mut rebuild_times = Vec::new();
    let mut calls = 0;
    let mut fallbacks = 0;
    let mut rebuilds = 0;
    let mut merges = 0;
    let mut splits = 0;
    let mut split_checks = 0;
    let mut component_runs = Vec::new();
    let mut root_runs = Vec::new();
    for edit in 0..options.edits {
        let source = &mut sources[file][node % model.functions];
        match kind {
            "leaf" => source.body ^= rng.random::<u64>() | 1,
            "sig" => source.sig ^= rng.random::<u64>() | 1,
            "edge" | "edge-cycle" => {
                if edit % 2 == 0 {
                    source.callees.push(extra);
                } else {
                    assert_eq!(source.callees.pop(), Some(extra));
                }
            }
            _ => unreachable!(),
        }
        files[file].set_text(&mut db).with_durability(Durability::LOW).to(sources[file].clone());
        db.counts.lock().unwrap().clear();
        let began = Instant::now();
        let (prints, timing) = if let Some(layer) = &mut reactive {
            layer.update(
                push.as_mut().unwrap(),
                &db,
                input,
                &[file],
                &options.signal,
                &options.topology,
            )
        } else if let Some(graph) = &mut push {
            let timing = graph.update(&db, input, &[file], &options.signal, &options.topology);
            (graph.prints.clone(), timing)
        } else {
            let prints = reach_program(&db, input).clone();
            (
                prints,
                PushTiming {
                    salsa_ms: began.elapsed().as_secs_f64() * 1000.,
                    ..PushTiming::default()
                },
            )
        };
        let total_ms = began.elapsed().as_secs_f64() * 1000.;
        peak_rss = peak_rss.max(rss());
        if let Some(layer) = &reactive {
            let (components, roots) = layer.counts();
            component_runs.push(components as f64);
            root_runs.push(roots as f64);
            eprintln!(
                "memos {} {kind} {edit}: component_runs={components} root_runs={roots}",
                options.scale
            );
        }
        let layer_ms = (total_ms - timing.salsa_ms).max(0.);
        times.push(total_ms);
        salsa_times.push(timing.salsa_ms);
        layer_times.push(layer_ms);
        rebuild_times.push(timing.rebuild_ms);
        calls += timing.calls;
        fallbacks += usize::from(timing.fallback);
        rebuilds += usize::from(timing.rebuilt);
        merges += timing.merges;
        splits += timing.splits;
        split_checks += timing.split_checks;
        eprintln!(
            "edit {} {} {} {kind} {edit}: total={total_ms:.3} ms salsa={:.3} ms layer={layer_ms:.3} ms codegen_calls={} topology={:.3} ms fallback_all={} mode={} merges={} splits={} split_checks={}",
            options.variant,
            options.signal,
            options.scale,
            timing.salsa_ms,
            timing.calls,
            timing.rebuild_ms,
            timing.fallback,
            options.topology,
            timing.merges,
            timing.splits,
            timing.split_checks
        );
        let counts = db.counts.lock().unwrap().clone();
        totals.push(counts.values().fold((0, 0), |a, b| (a.0 + b.0, a.1 + b.1)));
        for (ingredient, count) in counts {
            eprintln!(
                "edit {} {} {kind} {edit} {}: executed={} validated={}",
                options.variant,
                options.scale,
                db.ingredient_debug_name(ingredient),
                count.0,
                count.1
            );
            let total = ingredients.entry(ingredient).or_default();
            total.0 += count.0;
            total.1 += count.1;
        }
        assert_eq!(prints, reference(&model, &sources), "{kind} edit {edit} mismatch");
    }
    let first = times[0];
    let mut later = times[1..].to_vec();
    let later_median = quantile(&mut later, 0.5);
    let median = quantile(&mut times, 0.5);
    let p90 = quantile(&mut times, 0.9);
    let salsa_median = quantile(&mut salsa_times, 0.5);
    let layer_median = quantile(&mut layer_times, 0.5);
    let rebuild_median = quantile(&mut rebuild_times, 0.5);
    let bytes = push.as_ref().map_or(0, Push::bytes);
    let component_median =
        if component_runs.is_empty() { 0. } else { quantile(&mut component_runs, 0.5) };
    let root_median = if root_runs.is_empty() { 0. } else { quantile(&mut root_runs, 0.5) };
    let executed: u64 = totals.iter().map(|t| t.0).sum();
    let validated: u64 = totals.iter().map(|t| t.1).sum();
    println!(
        "| {} | {} | {} | {kind} | {cold_ms:.2} | {median:.2} | {p90:.2} | {first:.2} | {later_median:.2} | {executed} | {validated} | {cold_rss} | {salsa_median:.2} | {layer_median:.2} | {rebuild_median:.2} | {calls} | {bytes} | {fallbacks} | {rebuilds} | {} | {merges} | {splits} | {split_checks} | {reactive_rss} | {peak_rss} | {component_median:.0} | {root_median:.0} |",
        options.variant,
        if push.is_some() { &options.signal } else { "-" },
        options.scale,
        options.topology
    );
    for (index, (executed, validated)) in ingredients {
        let name = db.ingredient_debug_name(index);
        eprintln!(
            "counts {} {} {kind} {name}: executed={executed} validated={validated}",
            options.variant, options.scale
        );
    }
    eprintln!(
        "first {} {} {kind}: executed={} validated={}; later total: executed={} validated={}; correctness: {} edits matched",
        options.variant,
        options.scale,
        totals[0].0,
        totals[0].1,
        executed - totals[0].0,
        validated - totals[0].1,
        options.edits
    );
}

fn main() {
    let options = Options::parse();
    println!(
        "| variant | signal | scale | edit | cold ms | warm median ms | warm p90 ms | first ms | later median ms | executed (sum) | validated (sum) | cold RSS KiB | salsa median ms | layer median ms | topology median ms | codegen calls (sum) | native bytes | fallback edits | topology edits | topology mode | merges | splits | split checks | reactive RSS delta KiB | peak sampled RSS KiB | component runs median | root runs median |"
    );
    println!(
        "|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|"
    );
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            for kind in ["leaf", "edge", "edge-cycle", "sig"] {
                if options.edit == "all" || options.edit == kind {
                    run(&options, kind);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycles_and_disconnected_roots() {
        let model = Model {
            crates: 1,
            files: 1,
            functions: 3,
            roots: vec![0, 2],
            dependencies: vec![vec![]],
            signatures: vec![vec![]; 3],
        };
        let mut sources = vec![vec![
            FnSrc { sig: 1, body: 2, callees: vec![1] },
            FnSrc { sig: 3, body: 4, callees: vec![0] },
            FnSrc { sig: 5, body: 6, callees: vec![] },
        ]];
        let mut db = Db::default();
        let file = FileText::new(&db, sources[0].clone());
        let input = Input::new(&db, vec![file], model.clone());
        assert_eq!(*reach_program(&db, input), reference(&model, &sources));
        sources[0][0].body += 1;
        file.set_text(&mut db).to(sources[0].clone());
        assert_eq!(*reach_program(&db, input), reference(&model, &sources));
        sources[0][1].callees.push(2);
        file.set_text(&mut db).to(sources[0].clone());
        assert_eq!(*reach_program(&db, input), reference(&model, &sources));
        sources[0][2].sig += 1;
        file.set_text(&mut db).to(sources[0].clone());
        assert_eq!(*reach_program(&db, input), reference(&model, &sources));
    }

    #[test]
    fn empty_program() {
        let db = Db::default();
        let input = Input::new(
            &db,
            vec![],
            Model {
                crates: 0,
                files: 0,
                functions: 0,
                roots: vec![],
                dependencies: vec![],
                signatures: vec![],
            },
        );
        assert!(reach_program(&db, input).is_empty());
    }

    #[test]
    fn reported_quantiles() {
        let mut values = [4., 1., 3., 2.];
        assert_eq!(quantile(&mut values, 0.5), 2.5);
        assert_eq!(quantile(&mut values, 0.9), 4.);
    }

    #[test]
    fn push_edits_match_reference() {
        for durability in [Durability::LOW, Durability::MEDIUM] {
            for signal in ["all", "edit"] {
                let model = Model {
                    crates: 1,
                    files: 3,
                    functions: 2,
                    roots: vec![0, 1],
                    dependencies: vec![vec![]],
                    signatures: vec![vec![4]; 6],
                };
                let mut sources: Vec<Vec<_>> =
                    [vec![2, 3], vec![2], vec![3], vec![2], vec![5], vec![]]
                        .into_iter()
                        .enumerate()
                        .map(|(i, callees)| FnSrc { sig: i as u64, body: i as u64, callees })
                        .collect::<Vec<_>>()
                        .chunks(2)
                        .map(<[_]>::to_vec)
                        .collect();
                let mut db = Db::default();
                let files: Vec<_> = sources
                    .iter()
                    .map(|text| {
                        FileText::builder(text.clone()).text_durability(durability).new(&db)
                    })
                    .collect();
                let input = Input::new(&db, files.clone(), model.clone());
                let mut graph = Push::cold(&db, input);
                assert_eq!(graph.prints, reference(&model, &sources));
                assert!(graph.own[4].is_none());
                for step in 0..5 {
                    match step {
                        0 => sources[0][0].body += 1,
                        1 => sources[0][0].callees.push(4),
                        2 => sources[0][0].callees.clear(),
                        3 => sources[0][1].sig += 1,
                        4 => sources[0][1].callees.clear(),
                        _ => unreachable!(),
                    }
                    files[0]
                        .set_text(&mut db)
                        .with_durability(Durability::LOW)
                        .to(sources[0].clone());
                    db.counts.lock().unwrap().clear();
                    let timing = graph.update(&db, input, &[0], signal, "incremental");
                    assert_eq!(graph.prints, reference(&model, &sources), "{signal} step {step}");
                    assert_eq!(timing.fallback, signal == "edit" && step == 3);
                    assert_eq!(timing.rebuilt, matches!(step, 1 | 2 | 4));
                    for &index in db.counts.lock().unwrap().keys() {
                        assert!(!db.ingredient_debug_name(index).starts_with("reach_"));
                    }
                    assert!(graph.bytes() > 0);
                }
            }
        }
    }

    #[test]
    fn push_empty() {
        let db = Db::default();
        let input = Input::new(
            &db,
            vec![],
            Model {
                crates: 0,
                files: 0,
                functions: 0,
                roots: vec![],
                dependencies: vec![],
                signatures: vec![],
            },
        );
        let mut graph = Push::cold(&db, input);
        assert!(graph.prints.is_empty());
        assert_eq!(graph.update(&db, input, &[], "all", "incremental").calls, 0);
        assert_eq!(graph.update(&db, input, &[], "edit", "incremental").calls, 0);
    }

    fn check_topology(graph: &Push, model: &Model, sources: &[Vec<FnSrc>]) {
        assert_eq!(graph.prints, reference(model, sources));
        let reachable: Vec<_> =
            (0..model.count()).map(|node| Push::closure(node, &graph.edges)).collect();
        for (component, members) in graph.members.iter().enumerate() {
            let expected: FxHashSet<_> = members
                .iter()
                .flat_map(|&node| graph.edges[node].iter().map(|&to| graph.owner[to]))
                .filter(|&to| to != component)
                .collect();
            assert_eq!(graph.below[component].iter().copied().collect::<FxHashSet<_>>(), expected);
            for &to in &graph.below[component] {
                assert_eq!(graph.above[to].iter().filter(|&&from| from == component).count(), 1);
            }
            for &from in &graph.above[component] {
                assert!(graph.below[from].contains(&component));
            }
            for (root, &node) in model.roots.iter().enumerate() {
                assert_eq!(
                    graph.masks[component][root / 64] & (1 << (root % 64)) != 0,
                    members.iter().any(|member| reachable[node].contains(member))
                );
            }
        }
        for node in 0..model.count() {
            if graph.own[node].is_none() {
                continue;
            }
            assert!(graph.members[graph.owner[node]].contains(&node));
            for &to in &graph.edges[node] {
                assert!(graph.reverse[to].contains(&node));
            }
            for &from in &graph.reverse[node] {
                assert!(graph.edges[from].contains(&node));
            }
            for other in 0..model.count() {
                if graph.own[other].is_some() {
                    assert_eq!(
                        graph.owner[node] == graph.owner[other],
                        reachable[node].contains(&other) && reachable[other].contains(&node)
                    );
                }
            }
        }
    }

    #[test]
    fn incremental_merges_splits_new_subgraphs_and_restores() {
        let model = Model {
            crates: 1,
            files: 3,
            functions: 2,
            roots: vec![0, 2],
            dependencies: vec![vec![]],
            signatures: vec![vec![]; 6],
        };
        let mut sources: Vec<Vec<_>> = [vec![1], vec![2], vec![], vec![], vec![5], vec![4]]
            .into_iter()
            .enumerate()
            .map(|(i, callees)| FnSrc { sig: i as u64, body: i as u64, callees })
            .collect::<Vec<_>>()
            .chunks(2)
            .map(<[_]>::to_vec)
            .collect();
        let mut db = Db::default();
        let files: Vec<_> = sources.iter().map(|text| FileText::new(&db, text.clone())).collect();
        let input = Input::new(&db, files.clone(), model.clone());
        let mut graph = Push::cold(&db, input);
        let original = graph.prints.clone();
        assert!(graph.own[4].is_none());
        for (step, (node, edges)) in [
            (2, vec![0]),
            (2, vec![]),
            (0, vec![1, 4]),
            (0, vec![1]),
            (0, vec![1, 2]),
            (1, vec![]),
            (0, vec![1]),
            (1, vec![2]),
        ]
        .into_iter()
        .enumerate()
        {
            let file = model.file(node);
            sources[file][node % model.functions].callees = edges;
            files[file].set_text(&mut db).to(sources[file].clone());
            let timing = graph.update(&db, input, &[file], "edit", "incremental");
            check_topology(&graph, &model, &sources);
            if step == 0 {
                assert_eq!(timing.merges, 1);
                assert_eq!(graph.owner[0], graph.owner[2]);
            } else if step == 1 {
                assert_eq!(timing.splits, 1);
                assert_ne!(graph.owner[0], graph.owner[2]);
                assert_eq!(graph.prints, original);
            } else if step == 2 {
                assert!(graph.own[4].is_some());
                assert_eq!(graph.owner[4], graph.owner[5]);
            }
        }
        assert_eq!(graph.prints, original);
    }

    #[test]
    fn incremental_random_edits_match_reference() {
        for signal in ["all", "edit"] {
            for durability in [Durability::LOW, Durability::MEDIUM] {
                let model = Model {
                    crates: 1,
                    files: 4,
                    functions: 4,
                    roots: vec![0, 7],
                    dependencies: vec![vec![]],
                    signatures: vec![vec![15]; 16],
                };
                let mut sources = vec![vec![FnSrc { sig: 3, body: 5, callees: vec![] }; 4]; 4];
                let mut db = Db::default();
                let files: Vec<_> = sources
                    .iter()
                    .map(|text| {
                        FileText::builder(text.clone()).text_durability(durability).new(&db)
                    })
                    .collect();
                let input = Input::new(&db, files.clone(), model.clone());
                let mut graph = Push::cold(&db, input);
                let mut rng = StdRng::seed_from_u64(73);
                for step in 0..200 {
                    let node = rng.random_range(0..16);
                    let file = model.file(node);
                    let to = rng.random_range(0..16);
                    let source = &mut sources[file][node % model.functions];
                    if source.callees.contains(&to) {
                        source.callees.retain(|&edge| edge != to);
                    } else {
                        source.callees.push(to);
                    }
                    if step % 13 == 0 {
                        source.sig ^= 1;
                    }
                    files[file]
                        .set_text(&mut db)
                        .with_durability(Durability::LOW)
                        .to(sources[file].clone());
                    graph.update(&db, input, &[file], signal, "incremental");
                    check_topology(&graph, &model, &sources);
                }
            }
        }
    }

    #[test]
    fn reactive_diamonds_cycles_and_equal_writes() {
        let model = Model {
            crates: 1,
            files: 1,
            functions: 6,
            roots: vec![0, 4],
            dependencies: vec![vec![]],
            signatures: vec![vec![]; 6],
        };
        let mut sources = vec![
            [vec![1, 2], vec![3], vec![3], vec![], vec![5], vec![4]]
                .into_iter()
                .enumerate()
                .map(|(node, callees)| FnSrc { sig: node as u64, body: node as u64, callees })
                .collect::<Vec<_>>(),
        ];
        let mut db = Db::default();
        let file = FileText::new(&db, sources[0].clone());
        let input = Input::new(&db, vec![file], model.clone());
        let mut graph = Push::cold_layer(&db, input, false);
        let mut layer = Reactive::cold(&graph, &model.roots);
        assert_eq!(layer.pull(), reference(&model, &sources));
        assert_eq!(layer.counts(), (5, 2));
        layer.reset_counts();
        layer.signals[3].set(graph.own[3].unwrap());
        assert_eq!(layer.pull(), reference(&model, &sources));
        assert_eq!(layer.counts(), (1, 0));
        for step in 0..5 {
            match step {
                0 => sources[0][3].body += 1,
                1 => sources[0][3].sig += 1,
                2 => sources[0][3].callees.push(0),
                3 => sources[0][3].callees.clear(),
                4 => sources[0][0].callees.pop().map(|_| ()).unwrap(),
                _ => unreachable!(),
            }
            file.set_text(&mut db).to(sources[0].clone());
            let (prints, timing) =
                layer.update(&mut graph, &db, input, &[0], "edit", "incremental");
            assert_eq!(prints, reference(&model, &sources));
            if step == 0 {
                assert_eq!(layer.counts(), (4, 1));
            }
            assert_eq!(timing.rebuilt, step >= 2);
            assert_eq!(timing.fallback, step == 1);
        }
    }

    #[test]
    fn reactive_empty() {
        let db = Db::default();
        let input = Input::new(
            &db,
            vec![],
            Model {
                crates: 0,
                files: 0,
                functions: 0,
                roots: vec![],
                dependencies: vec![],
                signatures: vec![],
            },
        );
        let mut graph = Push::cold_layer(&db, input, false);
        let mut layer = Reactive::cold(&graph, &[]);
        assert!(layer.pull().is_empty());
        assert!(layer.update(&mut graph, &db, input, &[], "edit", "incremental").0.is_empty());
        assert_eq!(layer.counts(), (0, 0));
    }

    #[test]
    fn reactive_random_edits_match_reference() {
        for signal in ["all", "edit"] {
            let model = Model {
                crates: 1,
                files: 4,
                functions: 4,
                roots: vec![0, 7],
                dependencies: vec![vec![]],
                signatures: vec![vec![15]; 16],
            };
            let mut sources = vec![vec![FnSrc { sig: 3, body: 5, callees: vec![] }; 4]; 4];
            let mut db = Db::default();
            let files: Vec<_> = sources
                .iter()
                .map(|text| {
                    FileText::builder(text.clone()).text_durability(Durability::MEDIUM).new(&db)
                })
                .collect();
            let input = Input::new(&db, files.clone(), model.clone());
            let mut graph = Push::cold_layer(&db, input, false);
            let mut layer = Reactive::cold(&graph, &model.roots);
            assert_eq!(layer.pull(), reference(&model, &sources));
            let mut rng = StdRng::seed_from_u64(73);
            for step in 0..100 {
                let node = rng.random_range(0..16);
                let file = model.file(node);
                let to = rng.random_range(0..16);
                let source = &mut sources[file][node % model.functions];
                if source.callees.contains(&to) {
                    source.callees.retain(|&edge| edge != to);
                } else {
                    source.callees.push(to);
                }
                if step % 13 == 0 {
                    source.sig ^= 1;
                }
                files[file]
                    .set_text(&mut db)
                    .with_durability(Durability::LOW)
                    .to(sources[file].clone());
                let (prints, _) =
                    layer.update(&mut graph, &db, input, &[file], signal, "incremental");
                assert_eq!(prints, reference(&model, &sources));
            }
        }
    }
}
