//! Names for instances that are the same in every run of the daemon on the same sources, so
//! that code compiled by one run can be found by the next. A crate of the checkout is named
//! by what is written in it, so an edit makes other names of everything in it.

use std::{cell::RefCell, fmt::Write};

use hir_def::{
    AdtId, AssocItemId, CallableDefId, DefWithBodyId, FunctionId, HasModule, Lookup, ModuleDefId,
    StaticId, TraitId, expr_store::Body, item_scope::ItemScope, nameres::crate_def_map,
};
use hir_expand::{HirFileId, MacroCallKind};
use rustc_ast_ir::Mutability;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{
    AliasTy, AliasTyKind, BoundVarIndexKind, ExistentialPredicate, GenericArgKind, RegionKind,
    inherent::{IntoKind, Safety as _, Term as _},
};
use salsa::plumbing::FromId;
use span::ErasedFileAstId;

use base_db::Crate;

use super::{Instance, InstanceDef, SymbolResolver};
use crate::{
    ImplTraitId, InferBodyId,
    consteval::try_const_usize,
    db::{HirDatabase, InternedClosure, InternedClosureId, InternedCoroutineId},
    next_solver::{GenericArgs, Region, TermId, Ty, TyKind},
};

/// Before the content of a crate of the checkout, where a crate of rustc's alone has its id.
const OF_CHECKOUT: char = '~';

/// After the name of an instance compiled with `-C overflow-checks`.
const CHECKED: &str = " checked";

/// Before what stands for a crate from outside the checkout that rustc has no id for.
const OF_LIBRARY: char = '^';

enum Declared {
    Function(FunctionId),
    Static(StaticId),
}

/// Lowers what [`StableNames`] lists of `crates`, so that a build that lists them later
/// finds it done. `lower` is given the bodies of each round to lower at once.
pub fn lower_declared(db: &dyn HirDatabase, crates: &[Crate], lower: &dyn Fn(&[DefWithBodyId])) {
    declared(db, crates, lower, &mut |_| ());
}

/// The functions and statics `crates` declare, in their modules and in the blocks of their
/// bodies: a `static` is often written by a macro.
fn declared(
    db: &dyn HirDatabase,
    crates: &[Crate],
    lower: &dyn Fn(&[DefWithBodyId]),
    found: &mut dyn FnMut(Declared),
) {
    let mut bodies: Vec<DefWithBodyId> = Vec::new();
    let mut scope = |scope: &ItemScope, bodies: &mut Vec<DefWithBodyId>| {
        for def in scope.declarations() {
            match def {
                ModuleDefId::StaticId(id) => {
                    found(Declared::Static(id));
                    bodies.push(id.into());
                }
                ModuleDefId::FunctionId(id) => {
                    found(Declared::Function(id));
                    bodies.push(id.into());
                }
                ModuleDefId::ConstId(id) => bodies.push(id.into()),
                // A method a trait provides has blocks of its own.
                ModuleDefId::TraitId(id) => {
                    for &(_, item) in id.trait_items(db).items.iter() {
                        match item {
                            AssocItemId::FunctionId(id) => bodies.push(id.into()),
                            AssocItemId::ConstId(id) => bodies.push(id.into()),
                            AssocItemId::TypeAliasId(_) => {}
                        }
                    }
                }
                _ => {}
            }
        }
        bodies.extend(scope.unnamed_consts().map(DefWithBodyId::from));
        for imp in scope.impls() {
            for &(_, item) in imp.impl_items(db).items.iter() {
                match item {
                    AssocItemId::FunctionId(id) => {
                        found(Declared::Function(id));
                        bodies.push(id.into());
                    }
                    AssocItemId::ConstId(id) => bodies.push(id.into()),
                    AssocItemId::TypeAliasId(_) => {}
                }
            }
        }
    };
    for &krate in crates {
        for (_, module) in crate_def_map(db, krate).modules(db) {
            scope(module.scope(db), &mut bodies);
        }
    }
    while !bodies.is_empty() {
        let round = std::mem::take(&mut bodies);
        lower(&round);
        for body in round {
            for (_, def_map) in Body::of(db, body).blocks(db) {
                for (_, module) in def_map.modules(db) {
                    scope(module.scope(db), &mut bodies);
                }
            }
        }
    }
}

/// The statics and the functions without type parameters that one build of a crate declares.
#[derive(Default)]
struct Listed {
    statics: FxHashMap<String, StaticId>,
    functions: FxHashMap<String, Vec<FunctionId>>,
}

pub(super) struct StableNames<'a, 'db> {
    db: &'db dyn HirDatabase,
    symbols: &'a dyn SymbolResolver,
    /// The crates whose code changes under the daemon.
    owned: FxHashSet<Crate>,
    /// Whether what is of those crates has a name, by what is written in them now.
    by_content: bool,
    /// Where cargo keeps the sources it fetched on this machine.
    cargo_home: Option<String>,
    library: Option<super::LibrarySources>,
    files: RefCell<FxHashMap<HirFileId, Option<String>>>,
    /// The crates by what a name starts with, and what the ones asked about declare.
    crates: RefCell<Option<FxHashMap<String, Vec<Crate>>>>,
    listed: RefCell<FxHashMap<String, Listed>>,
    /// How often each thing kept an instance from having a name.
    pub(super) misses: RefCell<FxHashMap<&'static str, usize>>,
}

impl<'a, 'db> StableNames<'a, 'db> {
    pub(super) fn new(
        db: &'db dyn HirDatabase,
        symbols: &'a dyn SymbolResolver,
        owned: FxHashSet<Crate>,
        by_content: bool,
    ) -> Self {
        StableNames {
            db,
            symbols,
            owned,
            by_content,
            cargo_home: symbols.cargo_home(),
            library: symbols.library_sources(),
            files: RefCell::default(),
            crates: RefCell::default(),
            listed: RefCell::default(),
            misses: RefCell::default(),
        }
    }

    /// Whether a name is of anything of a crate of the checkout, which is only what the
    /// name says while the checkout is as it was: rustc's build of it can be of another time.
    pub(super) fn of_checkout(name: &str) -> bool {
        name.contains(OF_CHECKOUT)
    }

    /// `None` for an instance that names anything this has no stable name for.
    pub(super) fn instance(&self, instance: &Instance) -> Option<String> {
        let mut out = String::new();
        match instance.def {
            InstanceDef::Fn(func) => {
                out.push_str("fn ");
                self.function(&mut out, func)?;
            }
            InstanceDef::Closure(id) => {
                out.push_str("closure ");
                self.closure(&mut out, InternedClosureId::from_id(id).loc(self.db))?;
            }
            InstanceDef::Coroutine(id) => {
                out.push_str("coroutine ");
                self.closure(&mut out, InternedCoroutineId::from_id(id).loc(self.db))?;
            }
            InstanceDef::CoroutineByMove(id) => {
                out.push_str("coroutine by move ");
                self.closure(&mut out, InternedCoroutineId::from_id(id).loc(self.db))?;
            }
            InstanceDef::DropGlue => out.push_str("drop"),
            InstanceDef::CallOnceShim => out.push_str("call_once"),
            InstanceDef::VtableShim(func) => {
                out.push_str("vtable shim ");
                self.function(&mut out, func)?;
            }
            InstanceDef::FnPointerShim => out.push_str("fn_pointer"),
            InstanceDef::ReifyShim { receiver } => write!(out, "reify {receiver}").ok()?,
        }
        self.args(&mut out, instance.args.as_ref())?;
        if instance.checked {
            out.push_str(CHECKED);
        }
        Some(out)
    }

    /// The vtable of a type for a trait object, or the one with no methods.
    pub(super) fn vtable(
        &self,
        ty: Ty<'db>,
        trait_ref: Option<(TraitId, GenericArgs<'db>)>,
    ) -> Option<String> {
        let mut out = String::from("vtable ");
        self.ty(&mut out, ty)?;
        if let Some((trait_, args)) = trait_ref {
            out.push_str(" as ");
            self.trait_(&mut out, trait_)?;
            self.args(&mut out, args)?;
        }
        Some(out)
    }

    /// A static that [`Self::static_named`] finds again.
    pub(super) fn static_(&self, id: StaticId) -> Option<String> {
        let name = self.static_name(id)?;
        self.static_named(&name).is_some().then_some(name)
    }

    pub(super) fn static_named(&self, name: &str) -> Option<StaticId> {
        self.listed(name, |it| it.statics.get(name).copied())
    }

    /// The functions an instance without arguments can be of: one for each crate that the
    /// one build of its crate is here.
    pub(super) fn functions_named(&self, name: &str) -> Vec<FunctionId> {
        let name = name.strip_suffix(CHECKED).unwrap_or(name);
        // An instance of a library's function with a type of the checkout is asked about
        // too, and no function without type parameters is named so: its crate is not listed.
        let of_checkout = name.split_once(' ').is_some_and(|it| it.1.starts_with(OF_CHECKOUT));
        if !of_checkout {
            return Vec::new();
        }
        self.listed(name, |it| it.functions.get(name).cloned()).unwrap_or_default()
    }

    /// What the crate that `name` is of declares: a name starts with the kind of the item
    /// and the crate it is written in.
    fn listed<T>(&self, name: &str, of: impl FnOnce(&Listed) -> Option<T>) -> Option<T> {
        let (_, rest) = name.split_once(' ')?;
        let krate = &rest[..=rest.find(':')?];
        let mut listed = self.listed.borrow_mut();
        if !listed.contains_key(krate) {
            // One build of a crate can be several crates here, which differ in what the
            // daemon is told of them and not in what they declare.
            let mut crates = self.crates.borrow_mut();
            let crates = crates.get_or_insert_with(|| {
                let mut crates = FxHashMap::<String, Vec<Crate>>::default();
                // What is built names only what it depends on, and to name a crate of the
                // checkout is to go through every body of it: not of one that is not built.
                let named: FxHashSet<Crate> =
                    self.owned.iter().flat_map(|it| it.transitive_deps(self.db)).collect();
                let all = base_db::all_crates(self.db);
                for &krate in all.iter().filter(|it| named.contains(it)) {
                    let mut name = String::new();
                    if self.crate_(&mut name, krate).is_some() {
                        crates.entry(name).or_default().push(krate);
                    }
                }
                crates
            });
            let found = self.list(crates.get(krate)?);
            listed.insert(krate.to_owned(), found);
        }
        of(&listed[krate])
    }

    fn list(&self, crates: &[Crate]) -> Listed {
        let mut found = Listed::default();
        // Lowering a body is most of the listing, and the bodies do not wait on each other.
        let lower = |round: &[DefWithBodyId]| {
            self.symbols.in_parallel(round.len(), &|db, _, at| _ = Body::of(db, round[at]));
        };
        declared(self.db, crates, &lower, &mut |declared| match declared {
            Declared::Function(id) => {
                let mut name = String::from("fn ");
                if self.function(&mut name, id).is_some() {
                    name.push_str("<>");
                    found.functions.entry(name).or_default().push(id);
                }
            }
            Declared::Static(id) => {
                if let Some(name) = self.static_name(id) {
                    found.statics.entry(name).or_insert(id);
                }
            }
        });
        found
    }

    fn static_name(&self, id: StaticId) -> Option<String> {
        let mut out = String::from("static ");
        let at = id.lookup(self.db).id;
        self.item(&mut out, id.krate(self.db), at.file_id, at.value.erase())?;
        Some(out)
    }

    /// The name of a file as every machine has it: one of the standard library is where it
    /// was built, and one that cargo fetched is under [`super::CARGO_HOME`] whoever fetched
    /// it. `None` for a file that is already named so and is not one of those.
    fn stored(&self, path: String) -> Option<String> {
        if let Some(built) = self.library.as_ref().and_then(|it| it.stored(&path)) {
            return Some(built);
        }
        let home = self.cargo_home.as_deref();
        if home == Some(super::CARGO_HOME) {
            return Some(path);
        }
        if super::moved(&path, super::CARGO_HOME, "").is_some() {
            return None;
        }
        let there = home.and_then(|home| super::moved(&path, home, super::CARGO_HOME));
        Some(there.unwrap_or(path))
    }

    fn miss<T>(&self, why: &'static str) -> Option<T> {
        *self.misses.borrow_mut().entry(why).or_default() += 1;
        None
    }

    /// An item by where it is written: names do not tell two `impl`s apart.
    fn item(
        &self,
        out: &mut String,
        krate: Crate,
        file: HirFileId,
        id: ErasedFileAstId,
    ) -> Option<()> {
        self.crate_(out, krate)?;
        self.ast(out, file, id)
    }

    fn crate_(&self, out: &mut String, krate: Crate) -> Option<()> {
        // The source of a crate of the workspace changes too, built by the daemon or not.
        if self.owned.contains(&krate) || krate.data(self.db).origin.is_local() {
            if !self.by_content {
                return self.miss("of the checkout, in a patch");
            }
            let Some(id) = self.symbols.content_id(krate) else {
                return self.miss("no content id");
            };
            write!(out, "{OF_CHECKOUT}{id}:").ok()?;
        } else {
            match self.symbols.stable_crate_id(krate) {
                Some(id) => write!(out, "{id:x}:").ok()?,
                None => match self.symbols.content_id(krate) {
                    Some(id) => write!(out, "{OF_LIBRARY}{id}:").ok()?,
                    None => return self.miss("no crate id"),
                },
            }
        }
        Some(())
    }

    fn ast(&self, out: &mut String, file: HirFileId, id: ErasedFileAstId) -> Option<()> {
        if let Some(known) = self.files.borrow().get(&file) {
            out.push_str(known.as_deref()?);
        } else {
            let mut name = String::new();
            let named = self.file(&mut name, file);
            let name = named.map(|()| name);
            out.push_str(name.as_deref().unwrap_or_default());
            self.files.borrow_mut().insert(file, name);
            named?;
        }
        write!(out, "#{}", id.into_raw()).ok()
    }

    fn file(&self, out: &mut String, file: HirFileId) -> Option<()> {
        let named = |path: Option<String>| match path {
            Some(path) => self
                .stored(path)
                .or_else(|| self.miss("a file under what stands for cargo's directory")),
            None => self.miss("no source path"),
        };
        file_name(self.db, self.symbols, out, file, &named)
    }

    fn function(&self, out: &mut String, func: FunctionId) -> Option<()> {
        let id = func.lookup(self.db).id;
        self.item(out, func.krate(self.db), id.file_id, id.value.erase())
    }

    fn adt(&self, out: &mut String, adt: AdtId) -> Option<()> {
        let db = self.db;
        let (file, id) = match adt {
            AdtId::StructId(it) => {
                let id = it.lookup(db).id;
                (id.file_id, id.value.erase())
            }
            AdtId::UnionId(it) => {
                let id = it.lookup(db).id;
                (id.file_id, id.value.erase())
            }
            AdtId::EnumId(it) => {
                let id = it.lookup(db).id;
                (id.file_id, id.value.erase())
            }
        };
        self.item(out, adt.krate(db), file, id)
    }

    fn trait_(&self, out: &mut String, trait_: TraitId) -> Option<()> {
        let id = trait_.lookup(self.db).id;
        self.item(out, trait_.krate(self.db), id.file_id, id.value.erase())
    }

    /// A closure or an `async` block by the body it is written in and where.
    fn closure(&self, out: &mut String, closure: InternedClosure<'db>) -> Option<()> {
        let db = self.db;
        let InferBodyId::DefWithBodyId(owner) = closure.owner else {
            return self.miss("closure in an anonymous constant");
        };
        match owner {
            DefWithBodyId::FunctionId(it) => self.function(out, it)?,
            DefWithBodyId::ConstId(it) => {
                let id = it.lookup(db).id;
                self.item(out, it.krate(db), id.file_id, id.value.erase())?
            }
            DefWithBodyId::StaticId(it) => {
                let id = it.lookup(db).id;
                self.item(out, it.krate(db), id.file_id, id.value.erase())?
            }
            DefWithBodyId::VariantId(it) => {
                let id = it.lookup(db).id;
                self.item(out, it.krate(db), id.file_id, id.value.erase())?
            }
        }
        write!(out, "@{}", closure.expr.into_raw().into_u32()).ok()
    }

    fn args(&self, out: &mut String, args: GenericArgs<'db>) -> Option<()> {
        out.push('<');
        for arg in args.iter() {
            match arg.kind() {
                GenericArgKind::Lifetime(region) => self.region(out, region)?,
                GenericArgKind::Type(ty) => self.ty(out, ty)?,
                GenericArgKind::Const(konst) => {
                    if let Some(value) = try_const_usize(self.db, konst) {
                        write!(out, "{value}").ok()?
                    } else if let Some(value) = konst.try_to_value()
                        && let Some(leaf) = value.try_to_leaf()
                    {
                        self.ty(out, value.ty)?;
                        write!(out, ":{leaf:?}").ok()?
                    } else {
                        return self.miss("constant argument");
                    }
                }
            }
            out.push(',');
        }
        out.push('>');
        Some(())
    }

    /// Erased, unless a binder in the type binds it.
    fn region(&self, out: &mut String, region: Region<'db>) -> Option<()> {
        match region.kind() {
            RegionKind::ReBound(BoundVarIndexKind::Bound(depth), bound) => {
                write!(out, "'{}.{}", depth.as_u32(), bound.var.as_u32()).ok()
            }
            RegionKind::ReBound(..) => self.miss("bound region"),
            _ => {
                out.push_str("'_");
                Some(())
            }
        }
    }

    fn tys(&self, out: &mut String, tys: impl IntoIterator<Item = Ty<'db>>) -> Option<()> {
        for ty in tys {
            self.ty(out, ty)?;
            out.push(',');
        }
        Some(())
    }

    fn ty(&self, out: &mut String, ty: Ty<'db>) -> Option<()> {
        let db = self.db;
        match ty.kind() {
            TyKind::Bool => out.push_str("bool"),
            TyKind::Char => out.push_str("char"),
            TyKind::Str => out.push_str("str"),
            TyKind::Never => out.push('!'),
            TyKind::Int(it) => out.push_str(it.name_str()),
            TyKind::Uint(it) => out.push_str(it.name_str()),
            TyKind::Float(it) => out.push_str(it.name_str()),
            TyKind::Ref(region, pointee, mutability) => {
                out.push('&');
                self.region(out, region)?;
                out.push_str(match mutability {
                    Mutability::Not => " ",
                    Mutability::Mut => " mut ",
                });
                self.ty(out, pointee)?;
            }
            TyKind::RawPtr(pointee, mutability) => {
                out.push_str(match mutability {
                    Mutability::Not => "*const ",
                    Mutability::Mut => "*mut ",
                });
                self.ty(out, pointee)?;
            }
            TyKind::Slice(element) => {
                out.push('[');
                self.ty(out, element)?;
                out.push(']');
            }
            TyKind::Array(element, len) => {
                out.push('[');
                self.ty(out, element)?;
                let Some(len) = try_const_usize(db, len) else {
                    return self.miss("array length");
                };
                write!(out, ";{len}]").ok()?;
            }
            TyKind::Tuple(tys) => {
                out.push('(');
                self.tys(out, tys.iter())?;
                out.push(')');
            }
            TyKind::Adt(adt, args) => {
                out.push_str("adt ");
                self.adt(out, adt.def_id())?;
                self.args(out, args)?;
            }
            TyKind::FnDef(def, args) => {
                match def.0 {
                    CallableDefId::FunctionId(it) => {
                        out.push_str("fn ");
                        self.function(out, it)?;
                    }
                    CallableDefId::StructId(it) => {
                        out.push_str("ctor ");
                        self.adt(out, it.into())?;
                    }
                    CallableDefId::EnumVariantId(it) => {
                        out.push_str("ctor ");
                        let id = it.lookup(db).id;
                        self.item(out, it.krate(db), id.file_id, id.value.erase())?;
                    }
                }
                self.args(out, args)?;
            }
            TyKind::FnPtr(signature, header) => {
                write!(
                    out,
                    "fnptr {:?} {} {} (",
                    header.abi(),
                    header.safety().is_safe(),
                    header.c_variadic()
                )
                .ok()?;
                self.tys(out, signature.skip_binder().inputs_and_output.iter())?;
                out.push(')');
            }
            TyKind::Closure(id, args) => {
                out.push_str("closure ");
                self.closure(out, id.0.loc(db))?;
                self.args(out, args)?;
            }
            TyKind::CoroutineClosure(id, args) => {
                out.push_str("async closure ");
                self.closure(out, id.0.loc(db))?;
                self.args(out, args)?;
            }
            TyKind::Coroutine(id, args) => {
                out.push_str("coroutine ");
                self.closure(out, id.0.loc(db))?;
                self.args(out, args)?;
            }
            TyKind::Dynamic(predicates, region) => {
                // In an order of their own: the list is sorted by ids of this run.
                let mut written = Vec::new();
                for predicate in predicates.iter() {
                    let mut out = String::new();
                    match predicate.skip_binder() {
                        ExistentialPredicate::Trait(it) => {
                            out.push_str("trait ");
                            self.trait_(&mut out, it.def_id.0)?;
                            self.args(&mut out, it.args)?;
                        }
                        ExistentialPredicate::Projection(it) => {
                            let TermId::TypeAliasId(alias) = it.def_id.0 else {
                                return self.miss("projection");
                            };
                            out.push_str("type ");
                            let id = alias.lookup(db).id;
                            self.item(&mut out, alias.krate(db), id.file_id, id.value.erase())?;
                            self.args(&mut out, it.args)?;
                            out.push('=');
                            self.ty(&mut out, it.term.as_type()?)?;
                        }
                        ExistentialPredicate::AutoTrait(it) => {
                            out.push_str("auto ");
                            self.trait_(&mut out, it.0)?;
                        }
                    }
                    written.push(out);
                }
                written.sort();
                out.push_str("dyn (");
                for it in written {
                    out.push_str(&it);
                    out.push('+');
                }
                self.region(out, region)?;
                out.push(')');
            }
            // What was left of a projection that no `impl` in reach gives a type to.
            TyKind::Alias(AliasTy { kind: AliasTyKind::Projection { def_id }, args, .. }) => {
                let at = def_id.0.lookup(db).id;
                out.push_str("alias ");
                self.item(out, def_id.0.krate(db), at.file_id, at.value.erase())?;
                self.args(out, args)?;
            }
            // An `impl Trait` nothing has told the type of, as in the drop glue of what holds one.
            TyKind::Alias(AliasTy { kind: AliasTyKind::Opaque { def_id }, args, .. }) => {
                let (at, index) = match def_id.0.loc(db) {
                    ImplTraitId::ReturnTypeImplTrait(of, index) => {
                        out.push_str("opaque fn ");
                        self.function(out, of)?;
                        (None, index)
                    }
                    ImplTraitId::TypeAliasImplTrait(of, index) => {
                        out.push_str("opaque alias ");
                        (Some(of), index)
                    }
                };
                if let Some(of) = at {
                    let at = of.lookup(db).id;
                    self.item(out, of.krate(db), at.file_id, at.value.erase())?;
                }
                write!(out, " {}", index.into_raw().into_u32()).ok()?;
                self.args(out, args)?;
            }
            TyKind::Alias(..) => return self.miss("alias type"),
            TyKind::Param(..) => return self.miss("type parameter"),
            TyKind::CoroutineWitness(..) => return self.miss("coroutine witness"),
            TyKind::Foreign(def_id) => {
                let at = def_id.0.lookup(db).id;
                out.push_str("foreign ");
                self.item(out, def_id.0.krate(db), at.file_id, at.value.erase())?;
            }
            TyKind::Pat(..) => return self.miss("pattern type"),
            _ => return self.miss("other type"),
        }
        Some(())
    }
}

/// A file by its path as `named` has it, or for what a macro wrote by the call that wrote it.
fn file_name(
    db: &dyn HirDatabase,
    symbols: &dyn SymbolResolver,
    out: &mut String,
    file: HirFileId,
    named: &dyn Fn(Option<String>) -> Option<String>,
) -> Option<()> {
    let written_at = |out: &mut String, file: HirFileId, id: ErasedFileAstId| {
        file_name(db, symbols, out, file, named)?;
        write!(out, "#{}", id.into_raw()).ok()
    };
    match file {
        HirFileId::FileId(file) => out.push_str(&named(symbols.source_path(file.file_id(db)))?),
        HirFileId::MacroFile(call) => match &call.loc(db).kind {
            MacroCallKind::FnLike { ast_id, .. } => {
                written_at(out, ast_id.file_id, ast_id.value.erase())?;
                out.push('!');
            }
            MacroCallKind::Derive { ast_id, derive_attr_index, derive_index, .. } => {
                written_at(out, ast_id.file_id, ast_id.value.erase())?;
                write!(out, "!derive {derive_attr_index:?} {derive_index}").ok()?;
            }
            MacroCallKind::Attr { ast_id, censored_attr_ids, .. } => {
                written_at(out, ast_id.file_id, ast_id.value.erase())?;
                write!(out, "!attr {censored_attr_ids:?}").ok()?;
            }
        },
    }
    Some(())
}

/// Where a function inside a block is written, which its path does not say: two blocks of
/// one function, or two `const _` of one module, can each hold an item of the same name.
/// `None` for a function outside of any block.
pub fn block_place(
    db: &dyn HirDatabase,
    symbols: &dyn SymbolResolver,
    func: FunctionId,
) -> Option<String> {
    func.module(db).block(db)?;
    let id = func.lookup(db).id;
    let mut out = String::new();
    file_name(db, symbols, &mut out, id.file_id, &|path| path)?;
    write!(out, "#{}", id.value.erase().into_raw()).ok()?;
    Some(out)
}
