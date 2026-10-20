//! Answering an edit without writing the whole object again: the object of the last full build
//! stays as it is, and a small one with the functions that changed is linked ahead of it.
//!
//! The base gives its instances and statics names the patch can refer to. What the patch
//! defines under a name of the base replaces it there, for the linker takes the first
//! definition it sees. Whatever the patch can't express starts a full build over.

use std::{
    hash::{Hash, Hasher},
    sync::Arc,
};

use base_db::{Crate, FileId};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use hir_def::{FunctionId, HasModule, StaticId};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

type FxIndexMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;

use crate::{db::HirDatabase, traits::StoredParamEnvAndCrate};

use super::{
    CodegenError, Instance, ObjectCodegen, OwnStatics, Phases, Rejections, Result, Roots,
    SymbolResolver, TheirStatics, Walked, async_blocks, compiled_instance, compiled_root,
    compiled_static, declaration_location,
    fragment::{CompiledFunction, DataRequest, FuncTarget, Requests},
    home::{body_file, body_files},
    instance_serial, is_thread_local, left_to_rustc, root_serial, row_location, source_location,
    static_serial, target,
};

/// What a compiled function or static was when the base took it in.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct Mark {
    serial: u128,
    /// The source locations it reports, which stitching fills in.
    locations: u64,
    /// The lines its code is of, when a debugger is told them.
    lines: u64,
}

impl Mark {
    pub(super) fn new(db: &dyn HirDatabase, serial: u128, requests: &Requests) -> Mark {
        let mut hasher = rustc_hash::FxHasher::default();
        for request in &requests.datas {
            match request {
                DataRequest::Location(Some((owner, span))) => {
                    source_location(db, *owner, *span).hash(&mut hasher)
                }
                DataRequest::Declaration(func) => declaration_location(db, *func).hash(&mut hasher),
                _ => {}
            }
        }
        Mark { serial, locations: hasher.finish(), lines: 0 }
    }

    /// What a running program can tell of it.
    pub(super) fn seen(&self) -> (u128, u64) {
        (self.serial, self.locations)
    }

    /// The mark of a function, whose code is a patch's to describe again when `debug` is set
    /// and a line of it is another: an edit above it in the file moves them all.
    fn of_function(
        db: &dyn HirDatabase,
        serial: u128,
        compiled: &CompiledFunction,
        debug: bool,
    ) -> Mark {
        let mut hasher = rustc_hash::FxHasher::default();
        if debug && let Some((owner, spans)) = &compiled.source {
            for row in &compiled.code.lines {
                let span = spans.get(row.span as usize);
                span.map(|span| row_location(db, *owner, compiled.closure, *span))
                    .hash(&mut hasher);
            }
        }
        Mark { lines: hasher.finish(), ..Mark::new(db, serial, &compiled.requests) }
    }
}

/// Something in the base that an edit can change or take away.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Node {
    Root(FunctionId),
    Instance(Instance),
    Static(StaticId),
}

impl Node {
    fn is_asked_for_by(&self, requests: &Requests) -> bool {
        match self {
            Node::Root(_) => false,
            Node::Instance(instance) => requests.funcs.iter().any(
                |it| matches!(&it.target, FuncTarget::Instance(asked, _) if asked == instance),
            ),
            Node::Static(id) => requests
                .datas
                .iter()
                .any(|it| matches!(it, DataRequest::Static(asked) if asked == id)),
        }
    }
}

/// What a query gives for something of the base, or `None` when it panics: the edit may have
/// taken away what the base knew it by, and only looking tells. A build that is interrupted
/// goes on unwinding: that says nothing about the base. One that waited for a thread whose
/// own look panicked has found what that thread found.
fn probe<T>(query: impl FnOnce() -> T) -> Option<T> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(query)) {
        Ok(found) => Some(found),
        Err(stopped) => match stopped.downcast_ref::<salsa::Cancelled>() {
            Some(salsa::Cancelled::PropagatedPanic) | None => None,
            Some(_) => std::panic::resume_unwind(stopped),
        },
    }
}

#[derive(Clone)]
pub(super) struct BaseInstance {
    pub(super) env: StoredParamEnvAndCrate,
    pub(super) symbol: String,
    /// `None` when the base calls rustc's copy and compiling the instance failed.
    mark: Option<Mark>,
    forwarded: bool,
    /// The files whose bodies it comes from, or `None` when any may be one.
    files: Option<Box<[FileId]>>,
    /// What in the base refers to it.
    parents: Vec<Node>,
    /// The functions left to rustc reach it.
    theirs: bool,
}

/// An instance the functions left to rustc reach that the base has no code for.
#[derive(Clone)]
struct TheirInstance {
    instance: Instance,
    env: StoredParamEnvAndCrate,
    serial: Option<u128>,
    files: Option<Box<[FileId]>>,
}

/// A static the functions left to rustc reach that is rustc's.
#[derive(Clone)]
struct TheirStatic {
    id: StaticId,
    serial: Option<u128>,
    krate: Crate,
    file: FileId,
}

/// What the walk for [`TheirStatics`] went through, apart from the functions it starts at.
/// What it finds only changes with the code of one of these.
#[derive(Clone, Default)]
struct TheirWalk {
    instances: Vec<TheirInstance>,
    statics: Vec<TheirStatic>,
}

impl TheirWalk {
    /// Marks what of the base the walk went through, and keeps the rest.
    fn new(
        db: &dyn HirDatabase,
        found: &TheirStatics,
        walked: Walked,
        instances: &mut FxIndexMap<Instance, BaseInstance>,
        statics: &mut FxHashMap<StaticId, BaseStatic>,
    ) -> TheirWalk {
        instances.values_mut().for_each(|it| it.theirs = false);
        statics.values_mut().for_each(|it| it.theirs = false);
        let mut walk = TheirWalk::default();
        let mut seen = FxHashSet::default();
        for (instance, env) in walked {
            if let Some(known) = instances.get_mut(&instance)
                && known.env == env
            {
                known.theirs = true;
                continue;
            }
            if !seen.insert((instance.clone(), env.clone())) {
                continue;
            }
            let compiled = compiled_instance(db, instance.clone(), env.clone()).as_ref().ok();
            walk.instances.push(TheirInstance {
                serial: compiled.map(|_| instance_serial(db, instance.clone(), env.clone())),
                files: body_files(db, &instance),
                instance,
                env,
            });
        }
        for &id in &found.statics {
            if let Some(known) = statics.get_mut(&id) {
                known.theirs = true;
                continue;
            }
            walk.statics.push(TheirStatic {
                id,
                serial: compiled_static(db, id).as_ref().ok().map(|_| static_serial(db, id)),
                krate: id.krate(db),
                file: body_file(db, id.into()),
            });
        }
        walk
    }
}

#[derive(Clone)]
pub(super) struct BaseStatic {
    pub(super) symbol: String,
    pub(super) writable: bool,
    mark: Mark,
    krate: Crate,
    /// The file its value is written in.
    file: FileId,
    parents: Vec<Node>,
    /// The functions left to rustc reach it.
    theirs: bool,
}

/// What a function left to rustc keeps the rest of the build from doing.
#[derive(Clone, PartialEq, Eq)]
struct Left {
    /// Its code, when the function compiles and something else keeps it from the object.
    /// A full build looks at it again once that changes.
    code: Option<Mark>,
    async_blocks: Option<FxHashSet<salsa::Id>>,
}

impl Left {
    fn of(db: &dyn HirDatabase, root: FunctionId) -> Left {
        let code = compiled_root(db, root).as_ref().ok();
        Left {
            code: code.map(|it| Mark::new(db, root_serial(db, root), &it.requests)),
            async_blocks: async_blocks(db, root).clone(),
        }
    }
}

/// The functions left to rustc as rustc compiled them: its copies are not built again while
/// the daemon runs, so one is only good for as long as its function is what it was then.
#[derive(Clone, Default)]
pub(in crate::mir) struct Frozen {
    left: Option<FxHashMap<FunctionId, Left>>,
    /// The crates that have seen an edit since.
    edited: FxHashSet<Crate>,
    /// The files that have seen an edit to the bodies of functions alone, which can change
    /// no function written elsewhere.
    edited_bodies: FxHashSet<FileId>,
    /// The crates rustc compiled from other source than the daemon first saw them with: no
    /// copy of a function of theirs is good.
    distrusted: FxHashSet<Crate>,
}

impl Frozen {
    pub(in crate::mir) fn distrust(&mut self, crates: impl IntoIterator<Item = Crate>) {
        self.distrusted.extend(crates);
    }

    pub(in crate::mir) fn edit_bodies(&mut self, file: FileId) {
        self.edited_bodies.insert(file);
    }

    pub(in crate::mir) fn edit(&mut self, crates: impl IntoIterator<Item = Crate>) {
        self.edited.extend(crates);
    }

    /// A function of `base` that rustc's copy is no longer right for, and why.
    pub(in crate::mir) fn out_of_date(
        &mut self,
        db: &dyn HirDatabase,
        base: &Base,
    ) -> Option<(FunctionId, String)> {
        let now = || {
            let theirs = base.skipped.iter().filter(|it| !it.1.no_symbol());
            theirs.map(|(root, why)| (*root, why))
        };
        let distrusted = |root: FunctionId| self.distrusted.contains(&root.krate(db));
        let Some(left) = &self.left else {
            let other =
                now().find(|it| distrusted(it.0)).map(|(root, why)| (root, why.to_string()));
            self.left = Some(now().map(|(root, _)| (root, Left::of(db, root))).collect());
            return other;
        };
        now().find_map(|(root, why)| {
            let fresh = match left.get(&root) {
                _ if distrusted(root) => false,
                // Nothing to tell a change by: any edit that it can see may be one.
                Some(Left { code: None, .. }) => {
                    !self.edited.contains(&root.krate(db))
                        && !self.edited_bodies.contains(&body_file(db, root.into()))
                }
                Some(was) => probe(|| Left::of(db, root)).as_ref() == Some(was),
                None => false,
            };
            (!fresh).then(|| (root, why.to_string()))
        })
    }
}

/// The last object built in full, as far as patching it goes.
#[derive(Clone)]
pub(super) struct Base {
    /// Whether the object says which lines its code is of, as a patch of it then does.
    debug: bool,
    entries: Vec<FunctionId>,
    pub(super) compiled: Vec<(FunctionId, String)>,
    marks: Vec<Mark>,
    /// The crate of each of `compiled`, and the file it is written in.
    crates: Vec<Crate>,
    files: Vec<FileId>,
    touched: Touched,
    pub(super) skipped: Vec<(FunctionId, CodegenError)>,
    /// For each of `skipped` that rustc has a copy of.
    left: Vec<Option<Left>>,
    /// The skipped functions that rustc has a copy of.
    from_rustc: Vec<FunctionId>,
    their_statics: TheirStatics,
    their_walk: TheirWalk,
    pub(super) instances: FxIndexMap<Instance, BaseInstance>,
    homes: Homes,
    pub(super) statics: FxHashMap<StaticId, BaseStatic>,
    /// The symbols of the functions built from entries of the store, by their stable names.
    /// No edit reaches what those are compiled from.
    pub(super) found: FxHashMap<Arc<str>, String>,
    /// Some of `found` is code of the checkout, which an edit does reach, and nothing here
    /// tells what of it: the first edit takes a full build without any.
    hydrated: bool,
    outdated: bool,
    /// The instances that did not compile when the base was built. What called them was left
    /// to rustc, and stays there for as long as the base does.
    rejected: Vec<(Instance, StoredParamEnvAndCrate)>,
    pub(super) bodies: usize,
}

/// Where in the base the code of each crate is, and the code that comes from the bodies of
/// each file: an edit is looked for there, which is far less than the base.
#[derive(Clone, Default)]
struct Homes {
    root: FxHashMap<FunctionId, u32>,
    roots_of_crate: FxHashMap<Crate, Vec<u32>>,
    roots_of_file: FxHashMap<FileId, Vec<u32>>,
    instances_of_crate: FxHashMap<Crate, Vec<u32>>,
    instances_of_file: FxHashMap<FileId, Vec<u32>>,
    /// The instances that the bodies of any file may be part of.
    instances_of_any_file: Vec<u32>,
}

impl Homes {
    fn new(
        compiled: &[(FunctionId, String)],
        crates: &[Crate],
        files: &[FileId],
        instances: &FxIndexMap<Instance, BaseInstance>,
    ) -> Homes {
        let mut homes = Homes::default();
        for (i, &(root, _)) in compiled.iter().enumerate() {
            homes.root.insert(root, i as u32);
            homes.roots_of_crate.entry(crates[i]).or_default().push(i as u32);
            homes.roots_of_file.entry(files[i]).or_default().push(i as u32);
        }
        for (i, was) in instances.values().enumerate() {
            homes.instances_of_crate.entry(was.env.krate).or_default().push(i as u32);
            match &was.files {
                Some(files) => {
                    for &file in files {
                        homes.instances_of_file.entry(file).or_default().push(i as u32);
                    }
                }
                None => homes.instances_of_any_file.push(i as u32),
            }
        }
        homes
    }
}

/// One part in `parts` of `all`, in order and each once.
fn part_of(mut all: Vec<u32>, part: usize, parts: usize) -> impl Iterator<Item = usize> {
    all.sort_unstable();
    all.dedup();
    all.into_iter().skip(part).step_by(parts).map(|it| it as usize)
}

/// What an edit since the base was last looked at can have changed the code of, and what
/// differed from the base then, which does until an edit changes it back. Code compiled as a
/// crate depends on nothing but the files of that crate and of the ones it depends on. Of a
/// file where only the bodies of functions changed, and none of them is one that the rest of
/// the program sees into, it depends on no more than the bodies it comes from.
#[derive(Clone, Default)]
struct Touched {
    /// The crates that see a file that changed.
    crates: FxHashSet<Crate>,
    /// The files that changed in the bodies of functions alone.
    bodies: FxHashSet<FileId>,
    /// A file changed that we can't tell the crates of.
    any: bool,
    /// What the last look found changed.
    roots: FxHashSet<FunctionId>,
    instances: FxHashSet<Instance>,
    statics: FxHashSet<StaticId>,
}

impl Touched {
    fn reaches(&self, krate: Crate) -> bool {
        self.any || self.crates.contains(&krate)
    }

    /// Starts over from what a look at the whole base found: the edits before it can have
    /// changed nothing else.
    fn settle(&mut self, found: &[Stale]) {
        // A look that gave up, or that a thread did not come back from, did not get to
        // everything.
        if found.is_empty() || found.iter().any(|it| it.declined.is_some()) {
            return;
        }
        *self = Touched::default();
        for stale in found {
            self.roots.extend(&stale.roots);
            self.instances.extend(stale.instances.iter().cloned());
            self.statics.extend(&stale.statics);
            for (node, _) in &stale.broken {
                match node {
                    Node::Instance(instance) => _ = self.instances.insert(instance.clone()),
                    Node::Static(id) => _ = self.statics.insert(*id),
                    Node::Root(_) => {}
                }
            }
        }
    }

    fn reaches_bodies(&self, files: Option<&[FileId]>) -> bool {
        if self.bodies.is_empty() {
            return false;
        }
        files.is_none_or(|files| files.iter().any(|it| self.bodies.contains(it)))
    }
}

/// What a look at a part of the base found changed.
#[derive(Clone, Default)]
pub struct Stale {
    roots: Vec<FunctionId>,
    instances: Vec<Instance>,
    /// The statics with another value, which a patch defines again under their name.
    statics: Vec<StaticId>,
    /// What a patch can't replace, and why. That only matters for what the program still
    /// reaches.
    broken: Vec<(Node, &'static str)>,
    /// Why no patch can hold the change.
    declined: Option<&'static str>,
    /// Something the functions left to rustc reach changed, so what they reach may have.
    their_walk_changed: bool,
    pub steps: StaleSteps,
}

/// How long looking at each kind of thing in the base took, in the order they are looked at.
#[derive(Default, Clone, Copy)]
pub struct StaleSteps {
    pub roots: std::time::Duration,
    pub instances: std::time::Duration,
    pub statics: std::time::Duration,
    /// The functions left to rustc.
    pub left: std::time::Duration,
    /// How many roots and instances an edit could have changed, and so were asked about.
    pub roots_asked: usize,
    pub instances_asked: usize,
    /// The longest any one of them took to answer.
    pub slowest: std::time::Duration,
}

impl Stale {
    /// Declines when the functions the base left to rustc reach other statics than they did.
    fn declined(mut self, why: &'static str) -> Stale {
        self.declined = Some(why);
        self
    }
}

/// What of the base an edit left as it was: everything but these.
#[derive(Default)]
pub(super) struct Unchanged {
    pub(super) changed: FxHashSet<Node>,
    pub(super) broken: FxHashSet<Node>,
}

pub(super) struct Patch {
    pub(super) object: Vec<u8>,
    pub(super) bodies: usize,
    pub(super) phases: Phases,
}

/// An object that defines nothing.
pub(super) fn empty_object() -> Result<Vec<u8>> {
    let builder =
        ObjectBuilder::new(target()?.clone(), "rustd", cranelift_module::default_libcall_names())?;
    let object = ObjectModule::new(builder)
        .finish()
        .emit()
        .map_err(|e| CodegenError::Backend(e.to_string()))?;
    if super::Target::current().writes_wasm_objects() {
        return super::wasm_object::from_elf(&object, &Default::default())
            .map_err(CodegenError::Backend);
    }
    Ok(object)
}

impl Base {
    /// `None` when the build has something in it a patch could not keep track of.
    pub(super) fn record(
        db: &dyn HirDatabase,
        cg: &ObjectCodegen<'_, '_>,
        entries: &[FunctionId],
        compiled: &[(FunctionId, String)],
        skipped: &[(FunctionId, CodegenError)],
    ) -> Option<Base> {
        let decls = cg.module.declarations();
        let debug = cg.debug.is_some();
        let root_mark = |db: &dyn HirDatabase, root| {
            let compiled = compiled_root(db, root).as_ref().ok()?;
            Some(Mark::of_function(db, root_serial(db, root), compiled, debug))
        };
        let instance_mark =
            |db: &dyn HirDatabase, (instance, env): &(Instance, StoredParamEnvAndCrate)| {
                let compiled = compiled_instance(db, instance.clone(), env.clone()).as_ref().ok();
                let mark = compiled.map(|it| {
                    let serial = instance_serial(db, instance.clone(), env.clone());
                    Mark::of_function(db, serial, it, debug)
                });
                (mark, body_files(db, instance))
            };
        // The marks are a hash of each function's code and of its lines, which every thread
        // works out: the object waits for this.
        let (envs, roots) = (cg.envs.as_slice(), compiled.len());
        let root_marks: Vec<_> = (0..roots).map(|_| std::sync::OnceLock::new()).collect();
        let instance_marks: Vec<_> = envs.iter().map(|_| std::sync::OnceLock::new()).collect();
        cg.symbols.in_parallel(roots + envs.len(), &|db, _, at| match at.checked_sub(roots) {
            Some(at) => _ = instance_marks[at].set(instance_mark(db, &envs[at])),
            None => _ = root_marks[at].set(root_mark(db, compiled[at].0)),
        });
        let marks = compiled
            .iter()
            .zip(root_marks)
            .map(|(&(root, _), mark)| mark.into_inner().unwrap_or_else(|| root_mark(db, root)))
            .collect::<Option<Vec<_>>>()?;
        let mut instances = envs
            .iter()
            .zip(instance_marks)
            .map(|(of, mark)| {
                let (instance, env) = of;
                let id = *cg.instances.get(instance)?;
                let (mark, files) = mark.into_inner().unwrap_or_else(|| instance_mark(db, of));
                let known = BaseInstance {
                    env: env.clone(),
                    symbol: decls.get_function_decl(id).linkage_name(id).into_owned(),
                    mark,
                    forwarded: cg.forwarded.contains(instance),
                    files,
                    parents: Vec::new(),
                    theirs: false,
                };
                (known.mark.is_some() || known.forwarded).then(|| (instance.clone(), known))
            })
            .collect::<Option<FxIndexMap<_, _>>>()?;
        let mut statics = cg
            .statics
            .iter()
            .chain(&cg.frozen_statics)
            .map(|(&id, &data)| {
                let compiled = compiled_static(db, id).as_ref().ok()?;
                let known = BaseStatic {
                    symbol: decls.get_data_decl(data).linkage_name(data).into_owned(),
                    writable: compiled.writable,
                    mark: Mark::new(db, static_serial(db, id), &compiled.requests),
                    krate: id.krate(db),
                    file: body_file(db, id.into()),
                    parents: Vec::new(),
                    theirs: false,
                };
                Some((id, known))
            })
            .collect::<Option<FxHashMap<_, _>>>()?;
        let mut edges = Vec::new();
        let mut note = |parent: Node, requests: &Requests| {
            for request in &requests.funcs {
                if let FuncTarget::Instance(instance, _) = &request.target {
                    edges.push((Node::Instance(instance.clone()), parent.clone()));
                }
            }
            for request in &requests.datas {
                if let DataRequest::Static(id) = request {
                    edges.push((Node::Static(*id), parent.clone()));
                }
            }
        };
        for &(root, _) in compiled {
            note(Node::Root(root), &compiled_root(db, root).as_ref().ok()?.requests);
        }
        for (instance, known) in &instances {
            if let Ok(compiled) = compiled_instance(db, instance.clone(), known.env.clone()) {
                note(Node::Instance(instance.clone()), &compiled.requests);
            }
        }
        for &id in statics.keys() {
            note(Node::Static(id), &compiled_static(db, id).as_ref().ok()?.requests);
        }
        for (child, parent) in edges {
            let parents = match &child {
                Node::Root(_) => None,
                Node::Instance(instance) => instances.get_mut(instance).map(|it| &mut it.parents),
                Node::Static(id) => statics.get_mut(id).map(|it| &mut it.parents),
            };
            if let Some(parents) = parents {
                parents.push(parent);
            }
        }
        let left =
            skipped.iter().map(|(root, e)| (!e.no_symbol()).then(|| Left::of(db, *root))).collect();
        let from_rustc: Vec<FunctionId> = left_to_rustc(db, cg.symbols, skipped).collect();
        let (their_statics, walked) = TheirStatics::walk(db, from_rustc.iter().copied());
        let their_walk = TheirWalk::new(db, &their_statics, walked, &mut instances, &mut statics);
        let rejected = cg
            .rejected
            .iter()
            .filter(|(instance, it)| {
                compiled_instance(db, (*instance).clone(), it.env.clone()).is_err()
            })
            .map(|(instance, it)| (instance.clone(), it.env.clone()))
            .collect();
        let crates: Vec<Crate> = compiled.iter().map(|&(root, _)| root.krate(db)).collect();
        let files: Vec<FileId> =
            compiled.iter().map(|&(root, _)| body_file(db, root.into())).collect();
        Some(Base {
            debug,
            rejected,
            entries: entries.to_vec(),
            compiled: compiled.to_vec(),
            marks,
            homes: Homes::new(compiled, &crates, &files, &instances),
            crates,
            files,
            touched: Touched::default(),
            skipped: skipped.to_vec(),
            left,
            from_rustc,
            their_statics,
            their_walk,
            instances,
            statics,
            found: cg
                .found
                .iter()
                .map(|(name, id)| {
                    (name.clone(), decls.get_function_decl(*id).linkage_name(*id).into_owned())
                })
                .collect(),
            hydrated: cg
                .found
                .iter()
                .any(|(name, _)| super::stable::StableNames::of_checkout(name)),
            outdated: false,
            bodies: cg.bodies,
        })
    }

    /// Whether an edit changed code that the base has from the store, which no patch can
    /// replace.
    pub(super) fn outdated(&self) -> bool {
        self.outdated
    }

    /// Notes that a file changed: one of `crates`, or with `None` one we can't place.
    pub(super) fn touch(&mut self, db: &dyn HirDatabase, crates: Option<&[Crate]>) {
        let Some(crates) = crates else {
            self.touched.any = true;
            self.outdated |= self.hydrated;
            return;
        };
        for &krate in crates {
            if !self.touched.crates.contains(&krate) {
                self.touched.crates.extend(krate.transitive_rev_deps(db));
            }
        }
        self.outdated |=
            self.hydrated && self.crates.iter().any(|it| self.touched.crates.contains(it));
    }

    /// Notes that a file changed in the bodies of functions alone, none of which the rest of
    /// the program sees into.
    pub(super) fn touch_bodies(&mut self, db: &dyn HirDatabase, file: FileId) {
        self.touched.bodies.insert(file);
        self.outdated |= self.hydrated
            && base_db::relevant_crates(db, file).iter().any(|it| self.crates.contains(it));
    }

    /// Takes what every part of [`Base::stale`] found as where the next edit starts from.
    pub(super) fn settle(&mut self, db: &dyn HirDatabase, found: &mut [Stale]) {
        self.their_statics(db, found);
        self.touched.settle(found);
    }

    /// Declines when the functions the base left to rustc reach other statics than they did.
    /// Walking to them is slow, and nothing changes where the walk goes but the code of what
    /// it went through.
    fn their_statics(&mut self, db: &dyn HirDatabase, found: &mut [Stale]) {
        let check_all = std::env::var_os("RUSTD_CHECK_ALL").is_some();
        let changed = found.iter().any(|it| it.their_walk_changed);
        let Some(first) = found.first_mut() else { return };
        if !changed && !check_all {
            return;
        }
        let start = stdx::time::Instant::now();
        let now = probe(|| TheirStatics::walk(db, self.from_rustc.iter().copied()));
        match now {
            Some((now, walked)) if now == self.their_statics => {
                if changed {
                    self.their_walk =
                        TheirWalk::new(db, &now, walked, &mut self.instances, &mut self.statics);
                }
            }
            _ if !changed => eprintln!("check-all: MISSED statics of the functions left to rustc"),
            _ => first.declined = Some("the statics of a function left to rustc changed"),
        }
        first.steps.left += start.elapsed();
    }

    /// The roots an edit can have changed, or all of them, one part in `parts`.
    fn roots_to_ask(
        &self,
        all: bool,
        part: usize,
        parts: usize,
    ) -> Box<dyn Iterator<Item = usize> + '_> {
        let touched = &self.touched;
        if all || touched.any {
            return Box::new((part..self.compiled.len()).step_by(parts));
        }
        let homes = &self.homes;
        let of_crates = touched.crates.iter().filter_map(|it| homes.roots_of_crate.get(it));
        let of_files = touched.bodies.iter().filter_map(|it| homes.roots_of_file.get(it));
        let mut asked: Vec<u32> = of_crates.chain(of_files).flatten().copied().collect();
        asked.extend(touched.roots.iter().filter_map(|it| homes.root.get(it)));
        Box::new(part_of(asked, part, parts))
    }

    /// The instances an edit can have changed, or all of them, one part in `parts`.
    fn instances_to_ask(
        &self,
        all: bool,
        part: usize,
        parts: usize,
    ) -> Box<dyn Iterator<Item = usize> + '_> {
        let touched = &self.touched;
        if all || touched.any {
            return Box::new((part..self.instances.len()).step_by(parts));
        }
        let homes = &self.homes;
        let of_crates = touched.crates.iter().filter_map(|it| homes.instances_of_crate.get(it));
        let of_files = touched.bodies.iter().filter_map(|it| homes.instances_of_file.get(it));
        let mut asked: Vec<u32> = of_crates.chain(of_files).flatten().copied().collect();
        if !touched.bodies.is_empty() {
            asked.extend(&homes.instances_of_any_file);
        }
        asked.extend(
            touched
                .instances
                .iter()
                .filter_map(|it| self.instances.get_index_of(it))
                .map(|it| it as u32),
        );
        Box::new(part_of(asked, part, parts))
    }

    /// What one part in `parts` of the base no longer is what it was. Looking is most of the
    /// work of a patch, and the parts can be looked at on a thread each.
    pub(super) fn stale(&self, db: &dyn HirDatabase, part: usize, parts: usize) -> Stale {
        let start = stdx::time::Instant::now();
        let mut stale = Stale::default();
        let every = |len: usize| (part..len).step_by(parts);
        // A check of the skipping below: looks at what no edit can have changed too, and says
        // so if one did.
        let check_all = std::env::var_os("RUSTD_CHECK_ALL").is_some();
        for i in every(self.rejected.len()) {
            let (instance, env) = &self.rejected[i];
            let compiles = probe(|| compiled_instance(db, instance.clone(), env.clone()).is_ok());
            if compiles != Some(false) {
                return stale.declined("an instance that did not compile is another now");
            }
        }
        for i in self.roots_to_ask(check_all, part, parts) {
            let root = self.compiled[i].0;
            let touched = self.touched.reaches(self.crates[i])
                || self.touched.reaches_bodies(Some(&[self.files[i]]))
                || self.touched.roots.contains(&root);
            if !touched && !check_all {
                continue;
            }
            let asked = stdx::time::Instant::now();
            let mark = probe(|| {
                let compiled = compiled_root(db, root).as_ref().ok()?;
                Some(Mark::of_function(db, root_serial(db, root), compiled, self.debug))
            });
            stale.steps.roots_asked += 1;
            stale.steps.slowest = stale.steps.slowest.max(asked.elapsed());
            match mark {
                Some(Some(mark)) if mark == self.marks[i] => {}
                _ if !touched => {
                    eprintln!("check-all: MISSED root {root:?} of {:?}", self.crates[i]);
                    continue;
                }
                Some(Some(_)) => stale.roots.push(root),
                Some(None) => return stale.declined("a root of the base no longer compiles"),
                None => return stale.declined("a root of the base is gone"),
            }
        }
        stale.steps.roots = start.elapsed();
        for i in self.instances_to_ask(check_all, part, parts) {
            let Some((instance, was)) = self.instances.get_index(i) else { continue };
            let touched = self.touched.reaches(was.env.krate)
                || self.touched.reaches_bodies(was.files.as_deref())
                || self.touched.instances.contains(instance);
            if !touched && !check_all {
                continue;
            }
            let asked = stdx::time::Instant::now();
            let mark = probe(|| {
                let compiled = compiled_instance(db, instance.clone(), was.env.clone());
                compiled.as_ref().ok().map(|it| {
                    let serial = instance_serial(db, instance.clone(), was.env.clone());
                    Mark::of_function(db, serial, it, self.debug)
                })
            });
            stale.steps.instances_asked += 1;
            stale.steps.slowest = stale.steps.slowest.max(asked.elapsed());
            stale.their_walk_changed |= touched
                && was.theirs
                && mark.flatten().map(|it| it.serial) != was.mark.map(|it| it.serial);
            match mark {
                Some(mark) if mark == was.mark => {}
                _ if !touched => {
                    eprintln!("check-all: MISSED instance {instance:?} of {:?}", was.env.krate);
                    continue;
                }
                Some(Some(_)) if !was.forwarded => stale.instances.push(instance.clone()),
                // One that had no code of its own might have now.
                _ => stale.broken.push((
                    Node::Instance(instance.clone()),
                    "an instance of the base gained or lost code of its own",
                )),
            }
        }
        stale.steps.instances = start.elapsed() - stale.steps.roots;
        for (&id, was) in self.statics.iter().skip(part).step_by(parts) {
            let touched = self.touched.reaches(was.krate)
                || self.touched.reaches_bodies(Some(&[was.file]))
                || self.touched.statics.contains(&id);
            if !touched && !check_all {
                continue;
            }
            let mark = probe(|| {
                let compiled = compiled_static(db, id).as_ref().ok()?;
                Some(Mark::new(db, static_serial(db, id), &compiled.requests))
            });
            if mark == Some(Some(was.mark)) {
                continue;
            }
            if !touched {
                eprintln!("check-all: MISSED static {id:?} of {:?}", was.krate);
                continue;
            }
            stale.their_walk_changed |= was.theirs;
            // rustc's code has rustc's copy, and a thread's copy is laid out by the linker.
            let writable = probe(|| compiled_static(db, id).as_ref().ok().map(|it| it.writable));
            if writable == Some(Some(was.writable)) && !was.theirs && !is_thread_local(db, id) {
                stale.statics.push(id);
            } else {
                stale.broken.push((Node::Static(id), "a static of the base changed"));
            }
        }
        stale.steps.statics = start.elapsed() - stale.steps.roots - stale.steps.instances;
        for i in every(self.skipped.len()) {
            let Some(was) = &self.left[i] else { continue };
            let root = self.skipped[i].0;
            let touched = self.touched.reaches(root.krate(db))
                || self.touched.reaches_bodies(Some(&[body_file(db, root.into())]));
            if !touched && !check_all {
                continue;
            }
            if probe(|| Left::of(db, root)).as_ref() != Some(was) {
                if !touched {
                    eprintln!("check-all: MISSED function left to rustc {root:?}");
                    continue;
                }
                return stale.declined("a function left to rustc changed");
            }
        }
        for i in every(self.their_walk.instances.len()) {
            let was = &self.their_walk.instances[i];
            if !self.touched.reaches(was.env.krate)
                && !self.touched.reaches_bodies(was.files.as_deref())
            {
                continue;
            }
            let serial = probe(|| {
                let compiled = compiled_instance(db, was.instance.clone(), was.env.clone());
                compiled
                    .as_ref()
                    .ok()
                    .map(|_| instance_serial(db, was.instance.clone(), was.env.clone()))
            });
            stale.their_walk_changed |= serial != Some(was.serial);
        }
        for i in every(self.their_walk.statics.len()) {
            let was = &self.their_walk.statics[i];
            if !self.touched.reaches(was.krate) && !self.touched.reaches_bodies(Some(&[was.file])) {
                continue;
            }
            let serial = probe(|| {
                compiled_static(db, was.id).as_ref().ok().map(|_| static_serial(db, was.id))
            });
            stale.their_walk_changed |= serial != Some(was.serial);
        }
        stale.steps.left =
            start.elapsed() - stale.steps.roots - stale.steps.instances - stale.steps.statics;
        stale
    }

    /// Whether a root still refers to the node, directly or through others.
    fn reaches(&self, db: &dyn HirDatabase, node: &Node, unchanged: &Unchanged) -> bool {
        let mut seen = FxHashSet::default();
        let mut stack = vec![node];
        while let Some(node) = stack.pop() {
            let parents = match node {
                Node::Root(_) => return true,
                Node::Instance(instance) => self.instances.get(instance).map(|it| &it.parents),
                Node::Static(id) => self.statics.get(id).map(|it| &it.parents),
            };
            for parent in parents.into_iter().flatten() {
                if !seen.contains(parent) && self.still_asks_for(db, parent, node, unchanged) {
                    seen.insert(parent);
                    stack.push(parent);
                }
            }
        }
        false
    }

    /// Whether what referred to the node in the base does so after the edit.
    fn still_asks_for(
        &self,
        db: &dyn HirDatabase,
        parent: &Node,
        node: &Node,
        unchanged: &Unchanged,
    ) -> bool {
        // A broken parent that is reached stops the patch by itself.
        if unchanged.broken.contains(parent) {
            return false;
        }
        if !unchanged.changed.contains(parent) {
            return true;
        }
        let requests = match parent {
            Node::Root(root) => compiled_root(db, *root).as_ref().ok().map(|it| &it.requests),
            Node::Instance(instance) => self.instances.get(instance).and_then(|known| {
                let compiled = compiled_instance(db, instance.clone(), known.env.clone());
                compiled.as_ref().ok().map(|it| &it.requests)
            }),
            Node::Static(id) => compiled_static(db, *id).as_ref().ok().map(|it| &it.requests),
        };
        requests.is_some_and(|requests| node.is_asked_for_by(requests))
    }

    /// The futures that functions left to rustc handle, or `None` when that can be any.
    fn their_async_blocks(&self) -> Option<Option<FxHashSet<salsa::Id>>> {
        let mut theirs = Some(FxHashSet::default());
        let mut any = false;
        for left in self.left.iter().flatten() {
            any = true;
            theirs = theirs.zip(left.async_blocks.as_ref()).map(|(mut all, blocks)| {
                all.extend(blocks);
                all
            });
        }
        any.then_some(theirs)
    }

    /// An object with what changed since the base was built, or why the change is more than
    /// a patch can hold.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn patch(
        &self,
        db: &dyn HirDatabase,
        symbols: &dyn SymbolResolver,
        roots: Roots<'_>,
        on_demand: &FxHashSet<FunctionId>,
        denied: &FxHashSet<FunctionId>,
        known: &Rejections,
        own_statics: OwnStatics,
        stale: Vec<Stale>,
    ) -> Result<std::result::Result<Patch, &'static str>> {
        let start = stdx::time::Instant::now();
        if roots.entries != self.entries {
            return Ok(Err("the roots compiled whether called or not changed"));
        }
        let all: FxHashSet<FunctionId> =
            roots.entries.iter().chain(roots.on_demand).copied().collect();
        let known_roots =
            || self.compiled.iter().map(|it| it.0).chain(self.skipped.iter().map(|it| it.0));
        if !known_roots().all(|root| all.contains(&root)) {
            return Ok(Err("a root of the base is gone"));
        }

        let mut changed_roots = Vec::new();
        let mut changed_instances = Vec::new();
        let mut changed_statics = Vec::new();
        let mut broken = Vec::new();
        for part in stale {
            if let Some(why) = part.declined {
                return Ok(Err(why));
            }
            changed_roots.extend(part.roots);
            changed_instances.extend(part.instances);
            changed_statics.extend(part.statics);
            broken.extend(part.broken);
        }
        // What the edit took away is still in the base, where nothing refers to it any more.
        let unchanged = Unchanged {
            changed: changed_roots
                .iter()
                .map(|&root| Node::Root(root))
                .chain(changed_instances.iter().cloned().map(Node::Instance))
                .chain(changed_statics.iter().map(|&id| Node::Static(id)))
                .collect(),
            broken: broken.iter().map(|it| it.0.clone()).collect(),
        };
        if let Some((_, why)) = broken.iter().find(|it| self.reaches(db, &it.0, &unchanged)) {
            return Ok(Err(why));
        }
        changed_instances.retain(|it| self.reaches(db, &Node::Instance(it.clone()), &unchanged));
        changed_statics.retain(|&it| self.reaches(db, &Node::Static(it), &unchanged));
        let verify = start.elapsed();

        let mut cg = ObjectCodegen::new(
            db,
            symbols,
            &known.rejected,
            own_statics,
            on_demand,
            Some(self),
            false,
        )?;
        cg.phases.compile = verify;
        // What nothing reached any more can be reached again by the code compiled now.
        cg.replaced = unchanged;
        // rustc's copies are the ones the base was built against: what they call is in it.
        for instance in &changed_instances {
            let was = &self.instances[instance];
            let Ok(compiled) = compiled_instance(db, instance.clone(), was.env.clone()).as_ref()
            else {
                return Ok(Err("an instance of the base no longer compiles"));
            };
            let id = cg.module.declare_function(
                &was.symbol,
                Linkage::Hidden,
                &compiled.code.signature,
            )?;
            cg.instances.insert(instance.clone(), id);
            cg.pending.push((instance.clone(), was.env.clone(), id));
        }
        for &id in &changed_statics {
            if cg.static_data(id).is_err() {
                return Ok(Err("a static of the base no longer has a value"));
            }
        }
        let mut queued: FxHashSet<FunctionId> = known_roots().collect();
        let mut queue = changed_roots;
        queue.extend(cg.wanted.drain(..).filter(|&func| queued.insert(func)));
        let mut next = 0;
        loop {
            while let Some(&root) = queue.get(next) {
                next += 1;
                if denied.contains(&root)
                    || known.left.contains(&root)
                    || cg.define_function(root).is_err()
                {
                    return Ok(Err("a root can't be compiled"));
                }
                queue.extend(cg.wanted.drain(..).filter(|&func| queued.insert(func)));
            }
            if !cg.define_instances().is_empty() {
                return Ok(Err("an instance can't be compiled"));
            }
            queue.extend(cg.wanted.drain(..).filter(|&func| queued.insert(func)));
            if next == queue.len() {
                break;
            }
        }
        // A future is laid out by one compiler: a function that now handles one of rustc's
        // has to be left to rustc as well.
        if let Some(theirs) = self.their_async_blocks() {
            let shares = |root| match (async_blocks(db, root).clone(), &theirs) {
                (Some(ours), Some(theirs)) => !ours.is_disjoint(theirs),
                (Some(ours), None) => !ours.is_empty(),
                (None, _) => true,
            };
            if queue.iter().copied().any(shares) {
                return Ok(Err("a function now shares an `async` block with one left to rustc"));
            }
        }
        let (bodies, mut phases) = (cg.bodies, cg.phases);
        let start = stdx::time::Instant::now();
        let (object, _) = cg.finish()?;
        phases.object = start.elapsed();
        Ok(Ok(Patch { object, bodies, phases }))
    }
}

#[cfg(test)]
mod tests {
    use super::probe;

    #[test]
    fn a_probe_that_is_interrupted_goes_on_unwinding_and_one_that_panics_finds_nothing() {
        let gone: Option<()> = probe(|| panic!("the base no longer has it"));
        assert_eq!(gone, None);
        assert_eq!(probe(|| 7), Some(7));
        let waited: Option<()> =
            probe(|| std::panic::resume_unwind(Box::new(salsa::Cancelled::PropagatedPanic)));
        assert_eq!(waited, None);
        let interrupted = std::panic::catch_unwind(|| {
            probe(|| std::panic::resume_unwind(Box::new(salsa::Cancelled::PendingWrite)))
        });
        let stopped: Box<dyn std::any::Any + Send> = interrupted.unwrap_err();
        assert!(stopped.is::<salsa::Cancelled>());
    }
}
