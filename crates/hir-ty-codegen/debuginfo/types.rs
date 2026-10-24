//! What a debugger is told of the type of a variable: [`DebugType`]s from the types of a
//! function's locals.
//!
//! A number, a `bool`, a `char`, a pointer, an array, a tuple, a struct, a union and an enum
//! are told in full, an enum the way rustc tells of one, so that a debugger's printers for
//! `Option`, `Vec` and `String` find what they look for. A closure is told as a struct of
//! what it captured by the names of that, an `async` block as an enum of where it may have
//! left off with what it keeps there, and a pointer to a `dyn` as the pointer and the
//! vtable. Whatever else there is is told by name and size alone, which a debugger shows as
//! a value without fields.

use hir_def::{
    AdtId, EnumId, GenericDefId, VariantId, expr_store::ExpressionStore,
    hir::generics::GenericParamDataRef, item_tree::FieldsShape as Written,
};

use rustc_abi::{TagEncoding, Variants};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_type_ir::{
    UintTy,
    inherent::{BoundExistentialPredicates as _, GenericArgs as _, IntoKind},
};
use sha2::{Digest, Sha256};
use std::sync::{Arc, Mutex, Weak};

use super::super::vtable::{HEADER, VtableLayout};
use super::{Aggregate, DebugType, Field, Tag, TypeIndex, TypeList, TypeSet, Variant};
use crate::{
    InferenceResult, ParamEnvAndCrate,
    closure_analysis::ProjectionKind,
    consteval::try_const_usize,
    db::HirDatabase,
    db::InternedClosure,
    generics::generics,
    layout::CoroutineFrame,
    layout::struct_tail_erasing_lifetimes,
    layout::{Layout, RustcFieldIdx},
    mir::type_name::rustc_debug_name,
    next_solver::{
        DbInterner, GenericArgs, Ty, TyKind, TypingMode,
        infer::{DbInternerInferExt, InferCtxt, traits::ObligationCause},
        obligation_ctxt::ObligationCtxt,
    },
};

/// `DW_ATE_*`: how the bytes of a [`DebugType::Base`] are read.
mod encoding {
    pub(super) const BOOLEAN: u8 = 0x02;
    pub(super) const FLOAT: u8 = 0x04;
    pub(super) const SIGNED: u8 = 0x05;
    pub(super) const UNSIGNED: u8 = 0x07;
    pub(super) const UTF: u8 = 0x10;
}

/// How many pointers are followed from a variable before what one points to is left untold,
/// unless it is told of anyway: a list is as long as it likes.
const POINTERS: u32 = 2;

#[derive(Default)]
pub(in super::super) struct Descriptions(Mutex<FxHashMap<[u8; 32], Weak<[DebugType]>>>);

impl Descriptions {
    fn intern(&self, types: Vec<DebugType>) -> Arc<[DebugType]> {
        let Ok(bytes) = postcard::to_allocvec(&types) else { return types.into() };
        let key = Sha256::digest(bytes).into();
        let mut known = self.0.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(shared) = known.get(&key).and_then(Weak::upgrade)
            && shared.as_ref() == types.as_slice()
        {
            return shared;
        }
        let shared: Arc<[DebugType]> = types.into();
        known.insert(key, Arc::downgrade(&shared));
        shared
    }
}

/// The types of the variables of the functions of one environment. What a variable's type
/// is told as depends on nothing but the type, so it is found once for every function with
/// a variable of it: the layouts and the names are most of what telling of variables costs.
pub(in super::super) struct Types<'db> {
    sharing: super::super::Sharing,
    descriptions: Arc<Descriptions>,
    db: &'db dyn HirDatabase,
    env: ParamEnvAndCrate<'db>,
    interner: DbInterner<'db>,
    infcx: InferCtxt<'db>,
    /// What the type being described is made of so far, itself first.
    told: Vec<DebugType>,
    links: Vec<TypeSet>,
    /// Where each type that is told of, or is being told of, is among `told`.
    known: FxHashMap<Ty<'db>, TypeIndex>,
    described: FxHashMap<(Ty<'db>, u32), Option<TypeSet>>,
    roots: Vec<(Ty<'db>, u32)>,
    in_progress: FxHashSet<(Ty<'db>, u32)>,
    names: FxHashMap<Ty<'db>, Option<String>>,
    normalized: FxHashMap<Ty<'db>, Ty<'db>>,
}

impl<'db> Types<'db> {
    pub(in super::super) fn new(
        db: &'db dyn HirDatabase,
        env: ParamEnvAndCrate<'db>,
        descriptions: Arc<Descriptions>,
        sharing: super::super::Sharing,
    ) -> Self {
        let interner = DbInterner::new_with(db, env.krate);
        let infcx = interner.infer_ctxt().build(TypingMode::PostAnalysis);
        Types {
            sharing,
            descriptions,
            db,
            env,
            interner,
            infcx,
            told: Vec::new(),
            links: Vec::new(),
            known: FxHashMap::default(),
            described: FxHashMap::default(),
            roots: Vec::new(),
            in_progress: FxHashSet::default(),
            names: FxHashMap::default(),
            normalized: FxHashMap::default(),
        }
    }

    /// The type and every type it is made of, with the type itself first. `None` is a type
    /// that has no layout or no name rustc would spell.
    pub(in super::super) fn describe(&mut self, ty: Ty<'db>) -> Option<TypeSet> {
        self.describe_at(ty, POINTERS)
    }

    fn describe_at(&mut self, ty: Ty<'db>, pointers: u32) -> Option<TypeSet> {
        let root = (self.tellable(ty), pointers);
        if let Some(described) = self.described.get(&root) {
            return described.clone();
        }
        if !self.in_progress.insert(root) {
            return None;
        }
        let told = std::mem::take(&mut self.told);
        let known = std::mem::take(&mut self.known);
        let links = std::mem::take(&mut self.links);
        self.roots.push(root);
        let described = self.ty(root.0, pointers).map(|_| {
            TypeSet::new(TypeList {
                types: self.descriptions.intern(std::mem::take(&mut self.told)),
                links: std::mem::take(&mut self.links),
            })
        });
        self.roots.pop();
        self.in_progress.remove(&root);
        self.told = told;
        self.known = known;
        self.links = links;
        self.described.insert(root, described.clone());
        described
    }

    fn ty(&mut self, ty: Ty<'db>, pointers: u32) -> Option<TypeIndex> {
        // A type narrowed to some of its values, as what a `NonNull` keeps is, is told as
        // the type itself.
        let ty = self.tellable(ty);
        if let Some(&index) = self.known.get(&ty) {
            return Some(index);
        }
        let mut layout = None;
        let link = match ty.kind() {
            TyKind::Adt(..) => {
                let found = super::super::remap::layout(
                    self.db,
                    ty.store(),
                    self.env.store(),
                    self.sharing.clone(),
                )
                .ok()?;
                let link = !self.is_pointer(ty, found.size.bytes());
                layout = Some(found);
                link
            }
            TyKind::Closure(..) | TyKind::CoroutineClosure(..) | TyKind::Coroutine(..) => true,
            _ => false,
        };
        let root = (ty, pointers);
        if link && self.roots.last() != Some(&root) && !self.in_progress.contains(&root) {
            if let Some(described) = self.describe_at(ty, pointers) {
                let link = self
                    .links
                    .iter()
                    .position(|it| std::sync::Arc::ptr_eq(it, &described))
                    .unwrap_or_else(|| {
                        self.links.push(described);
                        self.links.len() - 1
                    });
                let index = self.told.len() as TypeIndex;
                self.told.push(DebugType::Link(link as u32));
                self.known.insert(ty, index);
                return Some(index);
            }
        }
        let layout = match layout {
            Some(layout) => layout,
            None => super::super::remap::layout(
                self.db,
                ty.store(),
                self.env.store(),
                self.sharing.clone(),
            )
            .ok()?,
        };
        let name = self.name(ty)?;
        // A type that is made of itself finds its place here. What stands there until the
        // type is told is what a type nothing more is known of is told as.
        let index = self.told.len() as TypeIndex;
        self.told.push(DebugType::Struct(Aggregate::opaque(name.clone(), layout.size.bytes())));
        self.known.insert(ty, index);
        let links = self.links.len();
        match self.told_as(ty, name, &layout, pointers) {
            Some(told) => self.told[index as usize] = told,
            // What was told since is of no use to anything.
            None => {
                self.told.truncate(index as usize);
                self.links.truncate(links);
                self.known.retain(|_, known| *known < index);
            }
        }
        self.known.get(&ty).copied()
    }

    /// What rustc calls the type, which is asked of every variable the type is part of.
    fn name(&mut self, ty: Ty<'db>) -> Option<String> {
        let db = self.db;
        self.names.entry(ty).or_insert_with(|| rustc_debug_name(db, ty)).clone()
    }

    fn told_as(
        &mut self,
        ty: Ty<'db>,
        name: String,
        layout: &Layout,
        pointers: u32,
    ) -> Option<DebugType> {
        let size = layout.size.bytes();
        let base = |name, encoding| Some(DebugType::Base { name, size, encoding });
        let mut of = Aggregate::opaque(name, size);
        match ty.kind() {
            TyKind::Bool => return base(of.name, encoding::BOOLEAN),
            TyKind::Char => return base(of.name, encoding::UTF),
            TyKind::Int(_) => return base(of.name, encoding::SIGNED),
            TyKind::Uint(_) => return base(of.name, encoding::UNSIGNED),
            TyKind::Float(_) => return base(of.name, encoding::FLOAT),
            TyKind::Ref(_, to, _) | TyKind::RawPtr(to, _) => {
                return self.pointer(of, to, pointers);
            }
            TyKind::Array(element, len) => {
                let len = try_const_usize(self.db, len)? as u64;
                return Some(DebugType::Array { of: self.ty(element, pointers)?, len });
            }
            TyKind::Tuple(tys) => {
                for (index, ty) in tys.iter().enumerate() {
                    let offset = layout.fields.offset(index).bytes();
                    // A field of a type that is not told of is left out.
                    if let Some(ty) = self.ty(ty, pointers) {
                        of.fields.push(Field { name: format!("__{index}"), offset, ty });
                    }
                }
            }
            TyKind::Closure(..) | TyKind::CoroutineClosure(..) => {
                let closure = match ty.kind() {
                    TyKind::Closure(id, _) => id.0.loc(self.db),
                    TyKind::CoroutineClosure(id, _) => id.0.loc(self.db),
                    _ => return None,
                };
                let upvars = ty.closure_upvars_ty()?;
                let offset_of = |it| layout.fields.offset(it).bytes();
                of.fields = self.captures(closure, upvars, offset_of, pointers);
            }
            TyKind::Coroutine(id, args) => {
                return self.coroutine(of, id, args, layout, pointers);
            }
            TyKind::Adt(_, _) if self.is_pointer(ty, size) => {
                return self.pointer(of, ty.boxed_ty()?, pointers);
            }
            TyKind::Adt(def, args) => {
                of.parameters = self.parameters(def.def_id().into(), args, pointers);
                match def.def_id() {
                    AdtId::StructId(id) => {
                        of.fields = self.fields(
                            id.into(),
                            args,
                            |it| layout.fields.offset(it).bytes(),
                            pointers,
                        )?;
                    }
                    AdtId::UnionId(id) => {
                        of.fields = self.fields(
                            id.into(),
                            args,
                            |it| layout.fields.offset(it).bytes(),
                            pointers,
                        )?;
                        return Some(DebugType::Union(of));
                    }
                    AdtId::EnumId(id) => return self.enumeration(of, id, args, layout, pointers),
                }
            }
            _ => {}
        }
        Some(DebugType::Struct(of))
    }

    /// The fields of a struct, a union or a variant of an enum, which `layout` is of.
    fn fields(
        &mut self,
        variant: VariantId,
        args: GenericArgs<'db>,
        offset_of: impl Fn(usize) -> u64,
        pointers: u32,
    ) -> Option<Vec<Field>> {
        let written = variant.fields(self.db);
        let tuple = written.shape == Written::Tuple;
        let mut fields = Vec::new();
        for (id, ty) in self.db.field_types(variant).iter() {
            let index = u32::from(id.into_raw()) as usize;
            let name = written.fields()[id].name.as_str();
            let name = if tuple { format!("__{name}") } else { name.to_owned() };
            let ty = ty.ty().instantiate(self.interner, args).skip_norm_wip();
            let offset = offset_of(index);
            if let Some(ty) = self.ty(ty, pointers) {
                fields.push(Field { name, offset, ty });
            }
        }
        Some(fields)
    }

    /// The types the generic parameters of `def` stand for in `args`, by the names the
    /// parameters are written with.
    fn parameters(
        &mut self,
        def: GenericDefId,
        args: GenericArgs<'db>,
        pointers: u32,
    ) -> Vec<(String, TypeIndex)> {
        let names: Vec<Option<String>> = generics(self.db, def)
            .iter_self()
            .map(|(_, parameter)| match parameter {
                GenericParamDataRef::TypeParamData(it) => {
                    it.name.as_ref().map(|name| name.as_str().to_owned())
                }
                _ => None,
            })
            .collect();
        let mut parameters = Vec::new();
        for (name, arg) in names.into_iter().zip(args.iter()) {
            if let Some(name) = name
                && let Some(ty) = arg.ty()
                && let Some(ty) = self.ty(ty, pointers)
            {
                parameters.push((name, ty));
            }
        }
        parameters
    }

    /// An enum: the names of its values when no variant has a field, and otherwise which
    /// variant a value is of by its tag and the fields of each.
    fn enumeration(
        &mut self,
        of: Aggregate,
        id: EnumId,
        args: GenericArgs<'db>,
        layout: &Layout,
        pointers: u32,
    ) -> Option<DebugType> {
        let written = &id.enum_variants(self.db).variants;
        let (tag, encoding, layouts) = match &layout.variants {
            Variants::Empty => return Some(DebugType::Struct(of)),
            Variants::Single { index } => {
                let (name, (variant, _)) = written.get_index(index.0)?;
                let offset_of = |it| layout.fields.offset(it).bytes();
                let fields = self.fields((*variant).into(), args, offset_of, pointers)?;
                let variant = Variant { name: name.as_str().to_owned(), tag: None, fields };
                return Some(DebugType::Enum { of, tag: None, variants: vec![variant] });
            }
            Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
                let size = tag.size(self.target()?).bytes();
                let offset = layout.fields.offset(rustc_index::Idx::index(*tag_field)).bytes();
                (Tag { offset, size, states: false }, tag_encoding, variants)
            }
        };
        // A tag is told as a number of a machine word at most.
        let mask = match tag.size {
            8 => u64::MAX,
            size @ 1..8 => (1 << (size * 8)) - 1,
            _ => return Some(DebugType::Struct(of)),
        };
        let mut variants = Vec::new();
        let mut fieldless = true;
        for (index, layout) in layouts.iter_enumerated() {
            let (name, (variant, _)) = written.get_index(index.0)?;
            let value = match encoding {
                TagEncoding::Direct => {
                    Some(self.db.const_eval_discriminant(*variant).ok()? as u64 & mask)
                }
                TagEncoding::Niche { untagged_variant, .. } if *untagged_variant == index => None,
                TagEncoding::Niche { niche_variants, niche_start, .. } => {
                    let nth = (index.0 - niche_variants.start.0) as u128;
                    Some(nth.wrapping_add(*niche_start) as u64 & mask)
                }
            };
            let offset_of = |it| layout.field_offsets[RustcFieldIdx::new(it)].bytes();
            let fields = self.fields((*variant).into(), args, offset_of, pointers)?;
            fieldless &= fields.is_empty();
            variants.push(Variant { name: name.as_str().to_owned(), tag: value, fields });
        }
        if fieldless && matches!(encoding, TagEncoding::Direct) {
            let names = variants.into_iter().filter_map(|it| Some((it.name, it.tag?))).collect();
            return Some(DebugType::Names { name: of.name, size: of.size, names });
        }
        Some(DebugType::Enum { of, tag: Some(tag), variants })
    }

    /// Whether a `Box` of `size` is nothing but the pointer, which it is told as then.
    fn is_pointer(&mut self, ty: Ty<'db>, size: u64) -> bool {
        let Some(to) = ty.boxed_ty() else { return false };
        let Some(word) = self.target().map(|it| it.pointer_size().bytes()) else { return false };
        let to = self.normalize(to);
        let wide = matches!(to.kind(), TyKind::Str | TyKind::Slice(_) | TyKind::Dynamic(..));
        size == if wide { 2 * word } else { word }
    }

    /// A pointer of one word, or of two as the struct rustc has for it: to a slice or a
    /// `str` where the first of them is and how many there are, to a `dyn` where the value is
    /// and the vtable of its type.
    fn pointer(&mut self, of: Aggregate, to: Ty<'db>, pointers: u32) -> Option<DebugType> {
        let to = self.normalize(to);
        let word = self.target()?.pointer_size().bytes();
        if of.size == word {
            return Some(DebugType::Pointer { name: of.name, to: self.followed(to, pointers) });
        }
        let usize = Ty::new_uint(self.interner, UintTy::Usize);
        let tail = self.tail(to);
        let (names, first, second) = match tail.kind() {
            TyKind::Str | TyKind::Slice(_) => {
                let first = match to.kind() {
                    TyKind::Slice(element) => element,
                    TyKind::Str => Ty::new_uint(self.interner, UintTy::U8),
                    _ => to,
                };
                let first = match first == to {
                    true => {
                        let name = format!("*const {}", self.name(to)?);
                        let whole = DebugType::Pointer { name, to: self.followed(to, pointers) };
                        self.unnamed(whole)
                    }
                    false => self.ty(Ty::new_imm_ptr(self.interner, first), pointers)?,
                };
                (["data_ptr", "length"], first, self.ty(usize, pointers)?)
            }
            TyKind::Dynamic(bounds, _) => {
                let value = DebugType::Pointer {
                    name: format!("*mut {}", self.name(to)?),
                    to: self.followed(to, pointers),
                };
                let slots = match bounds.principal() {
                    Some(principal) => {
                        let principal = principal.with_self_ty(self.interner, tail);
                        let principal =
                            self.interner.instantiate_bound_regions_with_erased(principal);
                        let interner = self.interner;
                        VtableLayout::of(interner, principal, &|it| {
                            super::super::vtable::without_lifetimes(interner, it)
                        })
                        .slots
                        .len()
                    }
                    None => 0,
                };
                let len = (HEADER + slots) as u64;
                let table = DebugType::Array { of: self.ty(usize, pointers)?, len };
                let table = self.unnamed(table);
                let table =
                    DebugType::Pointer { name: format!("&[usize; {len}]"), to: Some(table) };
                (["pointer", "vtable"], self.unnamed(value), self.unnamed(table))
            }
            _ => return Some(DebugType::Struct(of)),
        };
        let fields = vec![
            Field { name: names[0].to_owned(), offset: 0, ty: first },
            Field { name: names[1].to_owned(), offset: word, ty: second },
        ];
        Some(DebugType::Struct(Aggregate { fields, ..of }))
    }

    /// The part of a type whose size is not known until the program runs: the type, or the
    /// last field of a struct or a tuple, down to one that is neither.
    fn tail(&self, of: Ty<'db>) -> Ty<'db> {
        let normalize = |ty| {
            ObligationCtxt::new(&self.infcx)
                .structurally_normalize_ty(&ObligationCause::dummy(), self.env.param_env, ty)
                .unwrap_or(ty)
        };
        struct_tail_erasing_lifetimes(self.db, of, &normalize)
    }

    /// A type that is part of the one being told of and is no type of the program's.
    fn unnamed(&mut self, ty: DebugType) -> TypeIndex {
        self.told.push(ty);
        (self.told.len() - 1) as TypeIndex
    }

    /// What a closure or an `async` block captured, each by the name rustc has for it: the
    /// variable, the fields of it down to what is captured, and `_ref__` before one that is
    /// borrowed. `upvars` is the tuple of them, and one whose name is not known is told by
    /// its place there.
    fn captures(
        &mut self,
        closure: InternedClosure<'db>,
        upvars: Ty<'db>,
        offset_of: impl Fn(usize) -> u64,
        pointers: u32,
    ) -> Vec<Field> {
        let TyKind::Tuple(upvars) = upvars.kind() else { return Vec::new() };
        let names = self.capture_names(closure).filter(|names| names.len() == upvars.len());
        let mut fields = Vec::new();
        for (index, ty) in upvars.iter().enumerate() {
            let name = match &names {
                Some(names) => names[index].clone(),
                None => format!("__{index}"),
            };
            if let Some(ty) = self.ty(ty, pointers) {
                fields.push(Field { name, offset: offset_of(index), ty });
            }
        }
        fields
    }

    fn capture_names(&self, mut closure: InternedClosure<'db>) -> Option<Vec<String>> {
        if let crate::InferBodyId::DefWithBodyId(hir_def::DefWithBodyId::FunctionId(func)) =
            closure.owner
            && let Some(source) = self.sharing.analysis_source(self.db, func)
        {
            closure.owner = source.into();
        }
        let store = ExpressionStore::of(self.db, closure.owner.expression_store_owner(self.db));
        let infer = InferenceResult::of(self.db, closure.owner);
        let captured = infer.closures_data.get(&closure.expr)?.min_captures.values().flatten();
        captured
            .map(|capture| {
                let mut name = String::new();
                if capture.is_by_ref() {
                    name.push_str("_ref__");
                }
                name.push_str(store[capture.captured_local()].name.as_str());
                let mut base = capture.place.base_ty.as_ref();
                for projection in &capture.place.projections {
                    if let ProjectionKind::Field { field_idx, variant_idx } = projection.kind {
                        name.push_str("__");
                        name.push_str(&self.field_name(base, variant_idx, field_idx)?);
                    }
                    base = projection.ty.as_ref();
                }
                Some(name)
            })
            .collect()
    }

    /// The name of a field of a tuple, a struct or a variant of an enum.
    fn field_name(&self, of: Ty<'db>, variant: u32, field: u32) -> Option<String> {
        let TyKind::Adt(def, _) = of.kind() else { return Some(field.to_string()) };
        let variant: VariantId = match def.def_id() {
            AdtId::StructId(id) => id.into(),
            AdtId::UnionId(id) => id.into(),
            AdtId::EnumId(id) => {
                let variants = &id.enum_variants(self.db).variants;
                variants.get_index(variant as usize)?.1.0.into()
            }
        };
        let fields = variant.fields(self.db);
        let (_, field) = fields.fields().iter().nth(field as usize)?;
        Some(field.name.as_str().to_owned())
    }

    /// An `async` block, as rustc tells of one: an enum of not started, returned, panicked
    /// and each place it waits at, where it has the variables it keeps there, by their names.
    /// What it captured is in every one of them.
    fn coroutine(
        &mut self,
        of: Aggregate,
        id: crate::next_solver::CoroutineIdWrapper<'db>,
        args: GenericArgs<'db>,
        layout: &Layout,
        pointers: u32,
    ) -> Option<DebugType> {
        let Variants::Multiple { tag, tag_field, variants, .. } = &layout.variants else {
            return Some(DebugType::Struct(of));
        };
        let size = tag.size(self.target()?).bytes();
        let offset = layout.fields.offset(rustc_index::Idx::index(*tag_field)).bytes();
        let args = args.as_coroutine();
        let offset_of = |it| layout.fields.offset(it).bytes();
        let captured =
            self.captures(id.0.loc(self.db), args.tupled_upvars_ty(), offset_of, pointers);
        let parent_args = GenericArgs::new_from_slice(args.parent_args());
        use salsa::plumbing::AsId;
        let def = if self.sharing.coroutine_is_by_move(self.db, id.0, args) {
            super::super::InstanceDef::CoroutineByMove(id.0.as_id())
        } else {
            super::super::InstanceDef::Coroutine(id.0.as_id())
        };
        let body = super::super::program_instance_body(
            self.db,
            &super::super::Instance { def, args: parent_args.store(), checked: false },
            self.env.store(),
            &self.sharing,
        )
        .ok()?;
        let held = body.locals_held_across_yields(&self.infcx, self.env.param_env);
        let closure = id.0.loc(self.db);
        let store = ExpressionStore::of(self.db, closure.owner.expression_store_owner(self.db));
        let bindings = body.local_to_binding_map();
        let mut told = Vec::new();
        for (state, name) in ["Unresumed", "Returned", "Panicked"].into_iter().enumerate() {
            let fields = captured.clone();
            told.push(Variant { name: name.to_owned(), tag: Some(state as u64), fields });
        }
        let waiting = variants.iter().skip(CoroutineFrame::SUSPENDED);
        for (nth, (point, kept)) in held.yields.iter().zip(waiting).enumerate() {
            let mut fields = Vec::new();
            let awaited = body.awaited(point);
            for (field, &local) in point.kept.iter().enumerate() {
                let local = held.locals[local];
                // A value the body keeps without a name for it is not told of, but for the
                // future it waits for there, which rustc has a name for.
                let name = match bindings.get(local) {
                    Some(&binding) => store[binding].name.as_str(),
                    None if awaited == Some(local) => "__awaitee",
                    None => continue,
                };
                let offset = kept.field_offsets[RustcFieldIdx::new(field)].bytes();
                if let Some(ty) = self.ty(body.locals[local].ty.as_ref(), pointers) {
                    fields.push(Field { name: name.to_owned(), offset, ty });
                }
            }
            fields.extend(captured.iter().cloned());
            let tag = Some((CoroutineFrame::SUSPENDED + nth) as u64);
            told.push(Variant { name: format!("Suspend{nth}"), tag, fields });
        }
        Some(DebugType::Enum { of, tag: Some(Tag { offset, size, states: true }), variants: told })
    }

    /// What a pointer points to, where that is told of.
    fn followed(&mut self, to: Ty<'db>, pointers: u32) -> Option<TypeIndex> {
        match pointers.checked_sub(1) {
            Some(pointers) => self.ty(to, pointers),
            None => self.known.get(&to).copied(),
        }
    }

    fn target(&self) -> Option<&'db rustc_abi::TargetDataLayout> {
        self.db.target_data_layout(self.env.krate).ok()
    }

    fn normalize(&mut self, ty: Ty<'db>) -> Ty<'db> {
        if let Some(&normalized) = self.normalized.get(&ty) {
            return normalized;
        }
        let normalized = ObligationCtxt::new(&self.infcx)
            .structurally_normalize_ty(&ObligationCause::dummy(), self.env.param_env, ty)
            .unwrap_or(ty);
        self.normalized.insert(ty, normalized);
        normalized
    }

    fn tellable(&mut self, ty: Ty<'db>) -> Ty<'db> {
        let ty = self.normalize(ty);
        match ty.kind() {
            TyKind::Pat(of, _) => self.normalize(of),
            _ => ty,
        }
    }
}

impl Aggregate {
    /// A type nothing is told of but its name and its size.
    fn opaque(name: String, size: u64) -> Aggregate {
        Aggregate { name, size, fields: Vec::new(), parameters: Vec::new() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn description(name: &str) -> Vec<DebugType> {
        vec![DebugType::Base { name: name.to_owned(), size: 4, encoding: 7 }]
    }

    #[test]
    fn equal_descriptions_share_without_merging_sets() {
        let descriptions = Descriptions::default();
        let first = TypeSet::new(TypeList {
            types: descriptions.intern(description("Shared")),
            links: Vec::new(),
        });
        let mut types = description("Shared");
        types.reserve(100);
        let second = TypeSet::new(TypeList {
            types: descriptions.intern(types),
            links: vec![first.clone()],
        });
        assert!(Arc::ptr_eq(&first.types, &second.types));
        assert!(!Arc::ptr_eq(&first, &second));
        assert!(Arc::ptr_eq(&second.links[0], &first));
    }

    #[test]
    fn empty_descriptions_share() {
        let descriptions = Descriptions::default();
        let first = descriptions.intern(Vec::new());
        let second = descriptions.intern(Vec::new());
        assert!(first.is_empty());
        assert!(Arc::ptr_eq(&first, &second));
    }

    #[test]
    fn descriptions_do_not_keep_payloads_alive() {
        let descriptions = Descriptions::default();
        let first = descriptions.intern(description("Shared"));
        let weak = Arc::downgrade(&first);
        assert_eq!(Arc::strong_count(&first), 1);
        drop(first);
        assert!(weak.upgrade().is_none());
        let second = descriptions.intern(description("Shared"));
        assert_eq!(second.as_ref(), description("Shared"));
        assert_eq!(descriptions.0.lock().unwrap().len(), 1);
    }

    #[test]
    fn matching_hash_still_checks_content() {
        let descriptions = Descriptions::default();
        let first = descriptions.intern(description("First"));
        let other = description("Other");
        let key = Sha256::digest(postcard::to_allocvec(&other).unwrap()).into();
        descriptions.0.lock().unwrap().insert(key, Arc::downgrade(&first));
        let second = descriptions.intern(other.clone());
        assert!(!Arc::ptr_eq(&first, &second));
        assert_eq!(second.as_ref(), other);
    }

    #[test]
    fn descriptions_share_across_threads() {
        let descriptions = Arc::new(Descriptions::default());
        let first = descriptions.intern(description("Shared"));
        let second =
            std::thread::spawn(move || descriptions.intern(description("Shared"))).join().unwrap();
        assert!(Arc::ptr_eq(&first, &second));
    }
}
