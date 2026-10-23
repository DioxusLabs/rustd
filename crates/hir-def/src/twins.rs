//! Source twins and cfg observations; neither implies semantic equivalence.
//!
//! Rustc's `StripUnconfigured::{configure, process_cfg_attrs, configure_expr}` in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_expand/src/config.rs>
//! processes cfg_attr before gates and strips disabled nodes before their children.
//! These observations preserve RA's evaluation and include ancestor decisions;
//! opaque macro inputs are unknown rather than assumed independent of cfg.
//!
//! Expansion positions follow `MacroExpander::fully_expand_fragment` in rustc_expand/src/expand.rs
//! (same rustc tag). Output tokens are compared, not predicted from inputs. Context parents and
//! expansion marks are mapped as in rustc_span/src/hygiene.rs; unmappable marks reject a twin.
//! Derive placeholders accompany the original fragment in `fully_expand_fragment`;
//! derives append items rather than rewrite their input ADT.
//! Inert derive helpers follow the resolved DeriveHelper bindings constructed by
//! rustc_resolve/src/macros.rs at the same tag; their owning expansion is still compared.

use std::ops::ControlFlow;

use base_db::{Crate, EditionedFileId, SourceDatabase};
use cfg::{CfgOptions, CfgReads};
use hir_expand::{
    ErasedAstId, HirFileId, MacroCallId, MacroCallKind, MacroDefId, MacroDefKind,
    attrs::expand_cfg_attr,
};
use rustc_hash::{FxHashMap, FxHashSet};
use span::{ErasedFileAstId, SyntaxContext};
use syntax::{AstNode, SyntaxNode, ast};

use crate::{
    AdtId, AttrDefId, DefWithBodyId, HasModule, Lookup, MacroId, ModuleDefId,
    attrs::AttrFlags,
    expr_store::Body,
    item_scope::ItemScope,
    nameres::{DefMap, crate_def_map},
};

/// Source position used for twin matching and textual macro escape checks.
pub fn ast_id(db: &dyn SourceDatabase, item: AttrDefId) -> Option<ErasedAstId> {
    Some(match item {
        AttrDefId::ModuleId(id) => id.def_map(db).module(db, id).origin.declaration()?.erase(),
        AttrDefId::FunctionId(id) => id.lookup(db).id.erase(),
        AttrDefId::AdtId(AdtId::StructId(id)) => id.lookup(db).id.erase(),
        AttrDefId::AdtId(AdtId::UnionId(id)) => id.lookup(db).id.erase(),
        AttrDefId::AdtId(AdtId::EnumId(id)) => id.lookup(db).id.erase(),
        AttrDefId::EnumVariantId(id) => id.lookup(db).id.erase(),
        AttrDefId::ConstId(id) => id.lookup(db).id.erase(),
        AttrDefId::StaticId(id) => id.lookup(db).id.erase(),
        AttrDefId::TraitId(id) => id.lookup(db).id.erase(),
        AttrDefId::TypeAliasId(id) => id.lookup(db).id.erase(),
        AttrDefId::ImplId(id) => id.lookup(db).id.erase(),
        AttrDefId::MacroId(MacroId::MacroRulesId(id)) => id.lookup(db).id.erase(),
        AttrDefId::MacroId(MacroId::Macro2Id(id)) => id.lookup(db).id.erase(),
        AttrDefId::MacroId(MacroId::ProcMacroId(id)) => id.lookup(db).id.erase(),
        AttrDefId::ExternBlockId(id) => id.lookup(db).id.erase(),
        AttrDefId::ExternCrateId(id) => id.lookup(db).id.erase(),
        AttrDefId::UseId(id) => id.lookup(db).id.erase(),
    })
}

fn node(db: &dyn SourceDatabase, id: ErasedAstId) -> SyntaxNode {
    id.to_ptr(db).to_node(&id.file_id.parse_or_expand(db))
}

pub(crate) fn observe_attrs(
    owner: &ast::AnyHasAttrs,
    options: &CfgOptions,
    reads: &mut CfgReads,
) -> bool {
    observe_attrs_with(owner, options, reads, |_| false)
}

fn observe_attrs_with(
    owner: &ast::AnyHasAttrs,
    options: &CfgOptions,
    reads: &mut CfgReads,
    helper: impl Fn(&ast::Meta) -> bool,
) -> bool {
    use ast::HasAttrs as _;
    for attr in owner.attrs() {
        if attr.meta().is_none()
            || matches!(attr.meta(), Some(ast::Meta::CfgMeta(meta)) if meta.cfg_predicate().is_none())
            || matches!(attr.meta(), Some(ast::Meta::CfgAttrMeta(meta)) if meta.cfg_predicate().is_none())
        {
            reads.unknown = true;
        }
    }
    let enabled = AttrFlags::is_cfg_enabled_for(owner, options).is_ok();
    expand_cfg_attr::<()>(
        ast::attrs_including_inner(owner),
        || options,
        |meta, _| {
            if !matches!(meta, ast::Meta::CfgMeta(_)) {
                let name = meta
                    .path()
                    .and_then(|path| path.as_single_name_ref())
                    .map(|it| it.text().to_owned());
                if !name.as_deref().is_some_and(|name| {
                    matches!(
                        name,
                        "allow"
                            | "warn"
                            | "deny"
                            | "forbid"
                            | "expect"
                            | "doc"
                            | "inline"
                            | "cold"
                            | "test"
                            | "ignore"
                            | "should_panic"
                            | "must_use"
                            | "repr"
                            | "no_mangle"
                            | "export_name"
                            | "link_name"
                            | "track_caller"
                            | "thread_local"
                            | "deprecated"
                            | "non_exhaustive"
                            | "automatically_derived"
                            | "derive"
                            | "macro_export"
                            | "macro_use"
                            | "unsafe"
                    )
                }) && !helper(&meta)
                {
                    reads.unknown = true;
                }
            }
            ControlFlow::Continue(())
        },
    );
    enabled
}

/// Item/signature observations, including lexical and out-of-line module gates.
#[salsa::tracked(returns(ref))]
pub fn item_cfg_reads(db: &dyn SourceDatabase, item: AttrDefId) -> CfgReads {
    let krate = item.module(db).krate(db);
    let (options, recorder) = krate.cfg_options(db).recording();
    let mut reads = CfgReads::default();
    let observe = |owner: &ast::AnyHasAttrs, reads: &mut CfgReads| {
        observe_attrs_with(owner, &options, reads, |meta| {
            let Some(name) = meta.path().and_then(|path| path.as_single_name_ref()) else {
                return false;
            };
            let Some(adt) = owner.syntax().ancestors().find_map(ast::Adt::cast) else {
                return false;
            };
            let Some(id) = ast_id(db, item) else { return false };
            let map = id.file_id.ast_id_map(db);
            let adt_id = hir_expand::AstId::new(id.file_id, map.ast_id(&adt));
            item.module(db).def_map(db).derive_helpers_in_scope(adt_id).is_some_and(|helpers| {
                helpers.iter().any(|(helper, _, _)| helper.symbol().as_str() == name.text())
            })
        })
    };
    if let Some(attrs) = crate::attrs::parse_extra_crate_attrs(db, krate) {
        observe(&ast::AnyHasAttrs::new(attrs), &mut reads);
    }
    let Some(id) = ast_id(db, item) else {
        reads.unknown = true;
        return reads;
    };
    let syntax = node(db, id);
    let block = item.module(db).block(db).filter(|block| block.ast_id(db).file_id == id.file_id);
    let tree = if let Some(block) = block {
        Some(crate::item_tree::block_item_tree_query(db, unsafe { block.to_static() }, krate))
    } else if matches!(
        id.file_id.parse_or_expand(db).kind(),
        syntax::SyntaxKind::SOURCE_FILE
            | syntax::SyntaxKind::MACRO_ITEMS
            | syntax::SyntaxKind::MACRO_STMTS
    ) {
        Some(crate::item_tree::file_item_tree(db, id.file_id, krate))
    } else {
        reads.unknown = true;
        None
    };
    if let Some(recorded) = tree.and_then(|tree| tree.cfg_reads.get(&id.value)) {
        reads.merge(recorded);
    }
    for ancestor in syntax.ancestors() {
        if let Some(owner) = ast::AnyHasAttrs::cast(ancestor) {
            observe(&owner, &mut reads);
        }
    }
    let mut module = Some(item.module(db));
    while let Some(id) = module {
        let data = id.def_map(db).module(db, id);
        if let Some(source) = data.declaration_source(db) {
            for ancestor in source.value.syntax().ancestors() {
                if let Some(owner) = ast::AnyHasAttrs::cast(ancestor) {
                    observe(&owner, &mut reads);
                }
            }
        }
        let source = data.definition_source(db);
        if let crate::nameres::ModuleSource::SourceFile(file) = source.value {
            observe(&ast::AnyHasAttrs::new(file), &mut reads);
        }
        module = id.containing_module(db);
    }
    // Bodies and nested items have their own observations.
    let body = body(item)
        .and_then(|_| syntax.children().find_map(ast::Expr::cast))
        .map(|expr| expr.syntax().clone());
    let mut walk = syntax.preorder();
    while let Some(event) = walk.next() {
        if let syntax::WalkEvent::Enter(child) = event {
            if ast::MacroCall::can_cast(child.kind()) {
                reads.unknown = true;
                walk.skip_subtree();
            } else if child != syntax
                && (ast::Item::can_cast(child.kind()) || body.as_ref() == Some(&child))
            {
                walk.skip_subtree();
            } else if child != syntax
                && let Some(owner) = ast::AnyHasAttrs::cast(child)
                && !observe(&owner, &mut reads)
            {
                walk.skip_subtree();
            }
        }
    }
    reads.merge(&recorder.finish());
    reads
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FileKey {
    Source(EditionedFileId),
    Expansion(Box<CallKey>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AstKey {
    file: FileKey,
    id: ErasedFileAstId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CallKey {
    site: AstKey,
    kind: CallKindKey,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CallKindKey {
    Bang(bool, hir_expand::ExpandTo),
    Derive(hir_expand::attrs::AttrId, u32),
    Attr(Vec<hir_expand::attrs::AttrId>),
}

fn file_key(db: &dyn SourceDatabase, file: HirFileId, depth: usize) -> Option<FileKey> {
    if depth > 64 {
        return None;
    }
    Some(match file.macro_file() {
        Some(call) => FileKey::Expansion(Box::new(call_key(db, call, depth + 1)?)),
        None => FileKey::Source(file.file_id()?),
    })
}

fn ast_key(db: &dyn SourceDatabase, id: ErasedAstId, depth: usize) -> Option<AstKey> {
    Some(AstKey { file: file_key(db, id.file_id, depth)?, id: id.value })
}

fn call_key(db: &dyn SourceDatabase, call: MacroCallId, depth: usize) -> Option<CallKey> {
    let loc = call.loc(db);
    let (id, kind) = match &loc.kind {
        MacroCallKind::FnLike { ast_id, eager, expand_to } => {
            (ast_id.erase(), CallKindKey::Bang(eager.is_some(), *expand_to))
        }
        MacroCallKind::Derive { ast_id, derive_attr_index, derive_index, .. } => {
            (ast_id.erase(), CallKindKey::Derive(*derive_attr_index, *derive_index))
        }
        MacroCallKind::Attr { ast_id, censored_attr_ids, .. } => {
            (ast_id.erase(), CallKindKey::Attr(censored_attr_ids.iter().copied().collect()))
        }
    };
    Some(CallKey { site: ast_key(db, id, depth)?, kind })
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct SourceKey {
    id: AstKey,
    containers: Vec<AstKey>,
}

fn source_key(db: &dyn SourceDatabase, item: AttrDefId) -> Option<SourceKey> {
    let id = ast_id(db, item)?;
    let syntax = node(db, id);
    let map = id.file_id.ast_id_map(db);
    let mut containers: Vec<_> = syntax
        .ancestors()
        .skip(1)
        .filter_map(ast::Item::cast)
        .map(|item| ast_key(db, hir_expand::AstId::new(id.file_id, map.ast_id(&item)).erase(), 0))
        .collect::<Option<_>>()?;
    let mut module = Some(item.module(db));
    while let Some(id) = module {
        let data = id.def_map(db).module(db, id);
        if let Some(declaration) = data.origin.declaration() {
            containers.push(ast_key(db, declaration.erase(), 0)?);
        }
        module = id.containing_module(db);
    }
    Some(SourceKey { id: ast_key(db, id, 0)?, containers })
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct TwinIndex {
    /// T to N. These are source matches, not a shareable set.
    pub twins: FxHashMap<AttrDefId, AttrDefId>,
    pub unmatched: FxHashSet<AttrDefId>,
    pub test_only: FxHashSet<AttrDefId>,
    pub normal_only: usize,
    pub cfg_differing: usize,
    pub unknown: usize,
    pub function_bodies: TwinBodyCounts,
    pub cfg_differing_items: FxHashSet<AttrDefId>,
    pub unknown_items: FxHashSet<AttrDefId>,
    pub function_items: FxHashSet<AttrDefId>,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct TwinBodyCounts {
    pub twins: usize,
    pub cfg_differing: usize,
    pub test_only: usize,
    pub unmatched: usize,
    pub unknown: usize,
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

fn scope_items(db: &dyn SourceDatabase, scope: &ItemScope, items: &mut FxHashSet<AttrDefId>) {
    for item in scope.declarations() {
        let item = match item {
            ModuleDefId::ModuleId(id) => id.into(),
            ModuleDefId::FunctionId(id) => id.into(),
            ModuleDefId::AdtId(id) => id.into(),
            ModuleDefId::EnumVariantId(id) => id.into(),
            ModuleDefId::ConstId(id) => id.into(),
            ModuleDefId::StaticId(id) => id.into(),
            ModuleDefId::TraitId(id) => id.into(),
            ModuleDefId::TypeAliasId(id) => id.into(),
            ModuleDefId::MacroId(id) => id.into(),
            ModuleDefId::BuiltinType(_) => continue,
        };
        items.insert(item);
        match item {
            AttrDefId::TraitId(id) => items
                .extend(id.trait_items(db).items.iter().map(|(_, item)| AttrDefId::from(*item))),
            AttrDefId::AdtId(AdtId::EnumId(id)) => items
                .extend(id.enum_variants(db).variants.values().map(|(id, _)| AttrDefId::from(*id))),
            _ => (),
        }
    }
    for id in scope.impls() {
        items.insert(id.into());
        items.extend(id.impl_items(db).items.iter().map(|(_, item)| AttrDefId::from(*item)));
    }
    items.extend(scope.unnamed_consts().map(AttrDefId::from));
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct CrateItems {
    pub items: FxHashSet<AttrDefId>,
    pub definitions: FxHashMap<MacroDefId, AttrDefId>,
    pub scopes: Vec<crate::ModuleId>,
    body_calls: FxHashMap<DefWithBodyId, Vec<MacroCallId>>,
}

fn collect(db: &dyn SourceDatabase, map: &DefMap, items: &mut CrateItems) {
    for (id, module) in map.modules(db) {
        items.scopes.push(id);
        let scope = module.scope(db);
        scope_items(db, scope, &mut items.items);
        for id in scope
            .legacy_macros()
            .flat_map(|(_, ids)| ids.iter().copied())
            .chain(scope.macros().map(|(_, item)| item.def))
        {
            items.definitions.insert(id.definition(db), id.into());
        }
    }
}

#[salsa::tracked(returns(ref))]
pub fn crate_items(db: &dyn SourceDatabase, krate: Crate) -> CrateItems {
    let mut items = CrateItems::default();
    collect(db, crate_def_map(db, krate), &mut items);
    let mut seen = FxHashSet::default();
    loop {
        let pending: Vec<_> = items
            .items
            .iter()
            .copied()
            .filter_map(body)
            .filter(|item| seen.insert(*item))
            .collect();
        if pending.is_empty() {
            break;
        }
        for owner in pending {
            items.body_calls.insert(
                owner,
                Body::with_source_map(db, owner)
                    .1
                    .macro_calls()
                    .map(|(_, call)| call)
                    .filter(|call| {
                        !matches!(
                            call.loc(db).def.kind,
                            MacroDefKind::BuiltIn(
                                _,
                                hir_expand::builtin::BuiltinFnLikeExpander::Cfg
                            )
                        )
                    })
                    .collect(),
            );
            for (_, map) in Body::of(db, owner).blocks(db) {
                collect(db, map, &mut items);
            }
        }
    }
    items
}

pub fn scope_pairs(
    db: &dyn SourceDatabase,
    normal: Crate,
    test: Crate,
) -> Vec<(crate::ModuleId, crate::ModuleId)> {
    let key = |module: crate::ModuleId| {
        let mut keys = Vec::new();
        if let Some(block) = module.block(db) {
            keys.push(ast_key(db, block.ast_id(db).erase(), 0)?);
        }
        let mut next = Some(module);
        while let Some(module) = next {
            if let Some(declaration) = module.def_map(db).module(db, module).origin.declaration() {
                keys.push(ast_key(db, declaration.erase(), 0)?);
            }
            next = module.containing_module(db);
        }
        Some(keys)
    };
    let mut normals = FxHashMap::default();
    for &module in &crate_items(db, normal).scopes {
        if let Some(key) = key(module) {
            normals.entry(key).or_insert_with(Vec::new).push(module);
        }
    }
    crate_items(db, test)
        .scopes
        .iter()
        .filter_map(|&module| {
            let matches = normals.get(&key(module)?)?;
            (matches.len() == 1).then_some((matches[0], module))
        })
        .collect()
}

struct CallMatcher<'a> {
    db: &'a dyn SourceDatabase,
    normal: Crate,
    test: Crate,
    definitions: FxHashMap<MacroDefId, AttrDefId>,
    calls: FxHashMap<(MacroCallId, MacroCallId), bool>,
    active: FxHashSet<(MacroCallId, MacroCallId)>,
    pending: Vec<(MacroCallId, MacroCallId)>,
}

impl CallMatcher<'_> {
    fn contexts(&mut self, n: SyntaxContext, t: SyntaxContext, depth: usize) -> bool {
        if n == t {
            return true;
        }
        if depth > 64
            || n.edition(self.db) != t.edition(self.db)
            || n.outer_transparency(self.db) != t.outer_transparency(self.db)
        {
            return false;
        }
        match (n.outer_expn(self.db), t.outer_expn(self.db)) {
            (Some(nc), Some(tc)) => {
                self.call(nc.into(), tc.into())
                    && self.contexts(n.parent(self.db), t.parent(self.db), depth + 1)
            }
            _ => false,
        }
    }

    fn files(&mut self, n: HirFileId, t: HirFileId) -> bool {
        match (n.macro_file(), t.macro_file()) {
            (Some(n), Some(t)) => self.call(n, t),
            (None, None) => n == t,
            _ => false,
        }
    }

    fn origins(&mut self, n: AttrDefId, t: AttrDefId) -> bool {
        let files = |item| {
            let mut files: Vec<_> =
                ast_id(self.db, item).into_iter().map(|id| id.file_id).collect();
            let mut module = Some(item.module(self.db));
            while let Some(id) = module {
                if let Some(declaration) =
                    id.def_map(self.db).module(self.db, id).origin.declaration()
                {
                    files.push(declaration.file_id);
                }
                module = id.containing_module(self.db);
            }
            files
        };
        let (n, t) = (files(n), files(t));
        !n.is_empty() && n.len() == t.len() && n.into_iter().zip(t).all(|(n, t)| self.files(n, t))
    }

    fn definition(&mut self, n: MacroDefId, t: MacroDefId) -> bool {
        if n == t && n.krate != self.normal && n.krate != self.test {
            return true;
        }
        if n.krate != self.normal
            || t.krate != self.test
            || n.edition != t.edition
            || n.local_inner != t.local_inner
            || n.allow_internal_unsafe != t.allow_internal_unsafe
            || n.edition_panic != t.edition_panic
        {
            return false;
        }
        let kinds_agree = match (n.kind, t.kind) {
            (MacroDefKind::Declarative(_, n), MacroDefKind::Declarative(_, t)) => n == t,
            (MacroDefKind::BuiltIn(_, n), MacroDefKind::BuiltIn(_, t)) => n == t,
            (MacroDefKind::BuiltInAttr(_, n), MacroDefKind::BuiltInAttr(_, t)) => n == t,
            (MacroDefKind::BuiltInDerive(_, n), MacroDefKind::BuiltInDerive(_, t)) => n == t,
            (MacroDefKind::BuiltInEager(_, n), MacroDefKind::BuiltInEager(_, t)) => n == t,
            _ => false,
        };
        let (na, ta) = (n.kind.erased_ast_id(), t.kind.erased_ast_id());
        let key = ast_key(self.db, na, 0);
        if !kinds_agree
            || key.is_none()
            || key != ast_key(self.db, ta, 0)
            || !self.files(na.file_id, ta.file_id)
        {
            return false;
        }
        let (Some(&ni), Some(&ti)) = (self.definitions.get(&n), self.definitions.get(&t)) else {
            return false;
        };
        let key = source_key(self.db, ni);
        if key.is_none() || key != source_key(self.db, ti) || !self.origins(ni, ti) {
            return false;
        }
        let (nr, tr) = (item_cfg_reads(self.db, ni), item_cfg_reads(self.db, ti));
        !nr.unknown && !tr.unknown && nr == tr
    }

    fn tokens(&mut self, n: &tt::TopSubtree, t: &tt::TopSubtree) -> bool {
        let (n, t) = (
            n.view().as_token_trees().iter_flat_tokens(),
            t.view().as_token_trees().iter_flat_tokens(),
        );
        let mut pairs = n.zip(t);
        pairs.all(|(n, t)| {
            let mut span = |n: span::Span, t: span::Span| self.contexts(n.ctx, t.ctx, 0);
            match (n, t) {
                (tt::TokenTree::Subtree(n), tt::TokenTree::Subtree(t)) => {
                    n.len == t.len
                        && n.delimiter.kind == t.delimiter.kind
                        && span(n.delimiter.open, t.delimiter.open)
                        && span(n.delimiter.close, t.delimiter.close)
                }
                (
                    tt::TokenTree::Leaf(tt::Leaf::Ident(n)),
                    tt::TokenTree::Leaf(tt::Leaf::Ident(t)),
                ) => n.sym == t.sym && n.is_raw == t.is_raw && span(n.span, t.span),
                (
                    tt::TokenTree::Leaf(tt::Leaf::Literal(n)),
                    tt::TokenTree::Leaf(tt::Leaf::Literal(t)),
                ) => {
                    n.text_and_suffix == t.text_and_suffix
                        && n.kind == t.kind
                        && n.suffix_len == t.suffix_len
                        && span(n.span, t.span)
                }
                (
                    tt::TokenTree::Leaf(tt::Leaf::Punct(n)),
                    tt::TokenTree::Leaf(tt::Leaf::Punct(t)),
                ) => n.char == t.char && n.spacing == t.spacing && span(n.span, t.span),
                _ => false,
            }
        })
    }

    fn call(&mut self, n: MacroCallId, t: MacroCallId) -> bool {
        if let Some(&answer) = self.calls.get(&(n, t)) {
            return answer;
        }
        if self.active.contains(&(n, t)) {
            return true;
        }
        if self.active.len() > 64 {
            return false;
        }
        let (nl, tl) = (n.loc(self.db), t.loc(self.db));
        let key = call_key(self.db, n, 0);
        if key.is_none()
            || key != call_key(self.db, t, 0)
            || !(nl.krate == tl.krate || nl.krate == self.normal && tl.krate == self.test)
            || !self.definition(nl.def, tl.def)
        {
            return false;
        }
        self.active.insert((n, t));
        let ne = n.expansion_tokens(self.db);
        let te = t.expansion_tokens(self.db);
        let answer = ne.err.is_none()
            && te.err.is_none()
            && ne.value.view().as_token_trees().len() == te.value.view().as_token_trees().len()
            && self.files(nl.kind.file_id(), tl.kind.file_id())
            && self.contexts(nl.ctxt, tl.ctxt, 0)
            && self.tokens(&ne.value, &te.value);
        self.active.remove(&(n, t));
        self.calls.insert((n, t), answer);
        if answer {
            self.pending.push((n, t));
        }
        if self.active.is_empty() {
            // Roll back cycle-dependent successes if the outer proof failed.
            for pair in self.pending.drain(..) {
                if !answer {
                    self.calls.remove(&pair);
                }
            }
        }
        answer
    }
}

/// Whether the item or an ancestor is disabled under these cfg options.
pub fn gated_off(db: &dyn SourceDatabase, item: AttrDefId, options: &CfgOptions) -> bool {
    let disabled = |syntax: SyntaxNode| {
        syntax.ancestors().filter_map(ast::AnyHasAttrs::cast).any(|owner| {
            let mut test_attr = false;
            expand_cfg_attr::<()>(
                ast::attrs_including_inner(&owner),
                || options,
                |meta, _| {
                    test_attr |= meta
                        .path()
                        .and_then(|path| path.as_single_name_ref())
                        .is_some_and(|name| matches!(name.text(), "test" | "bench"));
                    ControlFlow::Continue(())
                },
            );
            AttrFlags::is_cfg_enabled_for(&owner, options).is_err()
                || test_attr && !options.check_atom(&cfg::CfgAtom::Flag(intern::sym::test))
        })
    };
    let disabled_origin = |mut id: ErasedAstId| {
        for _ in 0..64 {
            if disabled(node(db, id)) {
                return true;
            }
            let Some(call) = id.file_id.macro_file() else {
                break;
            };
            let kind = &call.loc(db).kind;
            id = ErasedAstId::new(kind.file_id(), kind.erased_ast_id());
        }
        false
    };
    if ast_id(db, item).is_some_and(disabled_origin) {
        return true;
    }
    let mut module = Some(item.module(db));
    while let Some(id) = module {
        let data = id.def_map(db).module(db, id);
        if data.origin.declaration().is_some_and(|source| disabled_origin(source.erase())) {
            return true;
        }
        module = id.containing_module(db);
    }
    false
}

fn expansion_input_reads(db: &dyn SourceDatabase, call: MacroCallId) -> CfgReads {
    let loc = call.loc(db);
    let (options, recorder) = loc.krate.cfg_options(db).recording();
    let mut reads = CfgReads::default();
    let syntax = loc.to_node_item(db).value.syntax().clone();
    let mut attrs = |owner: &ast::AnyHasAttrs| {
        use ast::HasAttrs as _;
        reads.unknown |= owner.attrs().any(|attr| attr.meta().is_none()
            || matches!(attr.meta(), Some(ast::Meta::CfgMeta(meta)) if meta.cfg_predicate().is_none())
            || matches!(attr.meta(), Some(ast::Meta::CfgAttrMeta(meta)) if meta.cfg_predicate().is_none()));
        AttrFlags::is_cfg_enabled_for(owner, &options).is_ok()
    };
    for ancestor in syntax.ancestors().skip(1).filter_map(ast::AnyHasAttrs::cast) {
        attrs(&ancestor);
    }
    let mut walk = syntax.preorder();
    while let Some(event) = walk.next() {
        if let syntax::WalkEvent::Enter(child) = event {
            if child != syntax && !matches!(loc.kind, MacroCallKind::Derive { .. }) {
                walk.skip_subtree();
            } else if let Some(owner) = ast::AnyHasAttrs::cast(child)
                && !attrs(&owner)
            {
                walk.skip_subtree();
            }
        }
    }
    reads.merge(&recorder.finish());
    reads
}

fn origin_reads(db: &dyn SourceDatabase, item: AttrDefId) -> CfgReads {
    let mut reads = reads(db, item).clone();
    let mut file = ast_id(db, item).map(|id| id.file_id);
    for _ in 0..64 {
        let Some(call) = file.and_then(|file| file.macro_file()) else {
            break;
        };
        reads.merge(&expansion_input_reads(db, call));
        file = Some(call.loc(db).kind.file_id());
    }
    reads
}

fn function_body(db: &dyn SourceDatabase, item: AttrDefId) -> bool {
    matches!(item, AttrDefId::FunctionId(_))
        && ast_id(db, item)
            .and_then(|id| ast::Fn::cast(node(db, id)))
            .is_some_and(|f| f.body().is_some())
}

fn reads(db: &dyn SourceDatabase, item: AttrDefId) -> &CfgReads {
    match body(item) {
        Some(owner) => Body::cfg_reads(db, owner),
        None => item_cfg_reads(db, item),
    }
}

#[salsa::tracked(returns(ref))]
pub fn twin_index(db: &dyn SourceDatabase, normal: Crate, test: Crate) -> TwinIndex {
    let mut result = TwinIndex::default();
    if normal == test || normal.root_file_id(db) != test.root_file_id(db) {
        return result;
    }
    let normal_items = crate_items(db, normal);
    let test_items = crate_items(db, test);
    let mut matcher = CallMatcher {
        db,
        normal,
        test,
        definitions: normal_items
            .definitions
            .iter()
            .chain(&test_items.definitions)
            .map(|(&k, &v)| (k, v))
            .collect(),
        calls: FxHashMap::default(),
        active: FxHashSet::default(),
        pending: Vec::new(),
    };
    let mut by_source = FxHashMap::default();
    for &item in &normal_items.items {
        if let Some(key) = source_key(db, item) {
            by_source.entry(key).or_insert_with(Vec::new).push(item);
        }
    }
    let mut matched = FxHashSet::default();
    for &item in &test_items.items {
        let is_body = usize::from(function_body(db, item));
        if is_body != 0 {
            result.function_items.insert(item);
        }
        if gated_off(db, item, normal.cfg_options(db)) {
            result.test_only.insert(item);
            result.function_bodies.test_only += is_body;
            continue;
        }
        let twin = source_key(db, item)
            .and_then(|key| by_source.get(&key))
            .filter(|items| items.len() == 1)
            .map(|items| items[0])
            .filter(|&twin| {
                let (Some(n), Some(t)) = (ast_id(db, twin), ast_id(db, item)) else {
                    return false;
                };
                node(db, n).kind() == node(db, t).kind() && matcher.origins(twin, item)
            });
        let Some(twin) = twin else {
            result.unmatched.insert(item);
            result.function_bodies.unmatched += is_body;
            continue;
        };
        matched.insert(twin);
        result.twins.insert(item, twin);
        let (mut n, mut t) = (origin_reads(db, twin), origin_reads(db, item));
        let mut macros_known = true;
        if let (Some(no), Some(to)) = (body(twin), body(item)) {
            let nc = &normal_items.body_calls[&no];
            let tc = &test_items.body_calls[&to];
            let mut keyed = FxHashMap::default();
            for &call in nc {
                if let Some(key) = call_key(db, call, 0) {
                    keyed.entry(key).or_insert_with(Vec::new).push(call);
                }
                n.merge(&expansion_input_reads(db, call));
            }
            macros_known &= nc.len() == tc.len();
            for &call in tc {
                t.merge(&expansion_input_reads(db, call));
                macros_known &= call_key(db, call, 0)
                    .and_then(|key| keyed.get(&key))
                    .filter(|calls| calls.len() == 1)
                    .is_some_and(|calls| matcher.call(calls[0], call));
            }
        }
        let differs = usize::from(
            n.differs_from(test.cfg_options(db)) || t.differs_from(normal.cfg_options(db)),
        );
        let unknown = usize::from(n.unknown || t.unknown || !macros_known);
        if differs != 0 {
            result.cfg_differing_items.insert(item);
        }
        if unknown != 0 {
            result.unknown_items.insert(item);
        }
        result.cfg_differing += differs;
        result.unknown += unknown;
        result.function_bodies.twins += is_body;
        result.function_bodies.cfg_differing += is_body * differs;
        result.function_bodies.unknown += is_body * unknown;
    }
    result.normal_only = normal_items.items.len() - matched.len();
    result
}

#[cfg(test)]
mod tests {
    use base_db::SourceDatabase;
    use intern::sym;
    use test_fixture::WithFixture;

    use super::*;
    use crate::test_db::TestDB;

    fn pair(fixture: &str) -> (TestDB, Crate, Crate) {
        let db = TestDB::with_files(fixture);
        let normal = db.fetch_test_crate();
        let mut options = normal.cfg_options(&db).clone();
        options.insert_atom(sym::test);
        let test = Crate::builder(
            normal.data(&db).clone(),
            normal.extra_data(&db).clone(),
            normal.workspace_data(&db).clone(),
            options,
            normal.env(&db).clone(),
        )
        .new(&db);
        (db, normal, test)
    }

    #[test]
    fn source_twins_and_unmatched() {
        let (db, normal, test) = pair(
            r#"
fn shared() {}
#[cfg(test)] fn only_test() {}
#[cfg(not(test))] fn only_normal() {}
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 1);
        assert_eq!(index.cfg_differing, 0);
        assert_eq!(index.test_only.len(), 1);
        assert!(index.unmatched.is_empty());
        assert_eq!(index.normal_only, 1);
        assert_eq!(index.unknown, 0);
    }

    #[test]
    fn pairs_module_and_block_scopes_without_test_only_scopes() {
        let (db, normal, test) = pair(
            r#"
mod common { pub struct Item; }
fn nested() { fn inner() {} }
#[cfg(test)] mod tests { fn only() {} }
"#,
        );
        let pairs = scope_pairs(&db, normal, test);
        assert_eq!(pairs.len(), crate_items(&db, normal).scopes.len());
        assert!(pairs.len() < crate_items(&db, test).scopes.len());
        assert!(pairs.iter().all(|(n, t)| n.krate(&db) == normal && t.krate(&db) == test));
    }

    #[test]
    fn item_body_and_ancestor_reads() {
        let (db, normal, test) = pair(
            r#"
//- minicore: cfg
//- /lib.rs crate:main
#[cfg_attr(test, inline)] fn attributed() {}
fn body() { #[cfg(test)] let x = 1; }
fn predicate() -> bool { cfg!(test) }
fn param(#[cfg(test)] x: u8) {}
struct S { #[cfg(test)] x: u8 }
#[cfg_attr(test, allow(dead_code))]
mod outer;
//- /outer.rs
fn child() {}
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 7);
        assert_eq!(index.cfg_differing, 7);
        assert_eq!(index.unknown, 0);
        assert!(index.unmatched.is_empty());
        for (t, n) in &index.twins {
            assert!(!reads(&db, *n).agrees_with(test.cfg_options(&db)));
            assert!(!reads(&db, *t).agrees_with(normal.cfg_options(&db)));
        }
    }

    #[test]
    fn containers_and_item_kinds() {
        let (db, normal, test) = pair(
            r#"
struct S;
enum E { V }
union U { x: u8 }
const C: u8 = 0;
static STATIC: u8 = 0;
type Alias = S;
trait Trait { const C: u8; type A; fn method(); }
impl Trait for S { const C: u8 = 0; type A = S; fn method() {} }
impl S { fn method() {} }
mod m { fn method() {} }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 19);
        assert!(index.unmatched.is_empty());
        assert_eq!(index.cfg_differing, 0);
        assert_eq!(index.unknown, 0);
        assert_eq!(index.twins.values().collect::<FxHashSet<_>>().len(), index.twins.len());
    }

    #[test]
    fn expression_cfg_sites() {
        let (db, normal, test) = pair(
            r#"
fn fields() { let _ = S { #[cfg(test)] x: 1 }; }
fn arms() { match 0 { #[cfg(test)] 0 => (), _ => () } }
fn closure() { let _ = |#[cfg(test)] x: u8| (); }
fn attr() { #[cfg_attr(test, cfg(any()))] let _ = 0; }
fn expr() { let _ = [#[cfg(test)] 1]; }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 5);
        assert_eq!(index.cfg_differing, 5);
        assert_eq!(index.unknown, 0);
    }

    #[test]
    fn key_value_and_short_circuit_reads() {
        let (db, normal, test) = pair(
            r#"
#[cfg_attr(all(feature = "x", test), inline)] fn f() {}
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.cfg_differing, 0);
        let item = *index.twins.values().next().unwrap();
        let reads = item_cfg_reads(&db, item);
        assert!(reads.atoms.is_empty());
        assert_eq!(reads.predicates.len(), 1);
        assert!(!reads.predicates[0].1);
    }

    #[test]
    fn exported_macro_expansion_twins() {
        let (db, normal, test) = pair(
            r#"
#[macro_export] macro_rules! value { () => { { const NAME: u32 = 1; NAME } } }
fn caller() -> u32 { value!() }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert!(index.unmatched.is_empty());
        assert!(index.unknown_items.is_empty());
        assert!(index.twins.keys().any(|id| matches!(id, AttrDefId::ConstId(_))));
    }

    #[test]
    fn generated_and_uncertain_items() {
        let (db, normal, test) = pair(
            r#"
macro_rules! make { () => { fn generated() {} } }
make!();
fn unresolved() { missing!(); }
macro_rules! value { () => { 0 } }
fn failed_expansion() { value!(unexpected); }
#[cfg()] fn malformed() {}
fn malformed_body() { #[cfg()] let _ = 0; }
fn opaque_body() { #[magic] let _ = 0; }
type Opaque = signature!();
type Sized = [u8; { cfg!(test) as usize }];
"#,
        );
        let index = twin_index(&db, normal, test);
        assert!(index.unmatched.is_empty());
        assert_eq!(index.cfg_differing, 0);
        assert_eq!(index.unknown, 7);
        assert!(index.twins.iter().any(|(t, n)| ast_id(&db, *t).unwrap().file_id.is_macro()
            && ast_id(&db, *n).unwrap().file_id.is_macro()));
    }

    #[test]
    fn cached_reads_and_edits() {
        let (mut db, normal, test) = pair(
            r#"
//- minicore: cfg
//- /lib.rs crate:main
fn shared() -> bool { false }
"#,
        );
        assert_eq!(twin_index(&db, normal, test).cfg_differing, 0);
        assert_eq!(twin_index(&db, normal, test).cfg_differing, 0);
        let file = normal.root_file_id(&db).file_id(&db);
        db.set_file_text(file, "fn shared() -> bool { cfg!(test) }");
        assert_eq!(twin_index(&db, normal, test).cfg_differing, 1);
        db.set_file_text(file, "fn shared() -> bool { cfg!(test) } #[cfg(test)] fn added() {}");
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 1);
        assert_eq!(index.cfg_differing, 1);
        assert_eq!(index.test_only.len(), 1);
    }

    #[test]
    fn no_pair() {
        let db = TestDB::with_files(
            r#"
//- /a.rs crate:a
fn f() {}
//- /b.rs crate:b
fn f() {}
"#,
        );
        let crates = base_db::all_crates(&db);
        assert!(twin_index(&db, crates[0], crates[1]).twins.is_empty());
        assert!(twin_index(&db, crates[0], crates[0]).twins.is_empty());
    }

    #[test]
    fn expanded_body_cfg_reads() {
        let (db, normal, test) = pair(
            r#"
//- minicore: cfg
//- /lib.rs crate:main
macro_rules! inner { () => { 0 } }
macro_rules! plain { () => { inner!() } }
macro_rules! predicate { () => { cfg!(test) } }
macro_rules! gate { () => {{ #[cfg(test)] let x = 0; }} }
fn shared() { plain!(); }
fn differing() { predicate!(); }
fn gated() { gate!(); }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 3);
        assert_eq!(index.cfg_differing, 2);
        assert_eq!(index.unknown, 0);
        assert!(index.unmatched.is_empty());
    }

    #[test]
    fn changed_macro_definition_is_unknown() {
        let (db, normal, test) = pair(
            r#"
#[cfg(not(test))] macro_rules! value { () => { 0 } }
#[cfg(test)] macro_rules! value { () => { 1 } }
fn f() { value!(); }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 1);
        assert_eq!(index.unknown, 1);
    }

    #[test]
    fn proc_macro_and_derive_twins() {
        let (db, normal, test) = pair(
            r#"
//- proc_macros: identity, mirror, derive_identity
//- minicore: derive
//- /lib.rs crate:main
#[proc_macros::identity]
fn generated() {}
fn expanded() { proc_macros::mirror!(0); }
#[derive(proc_macros::DeriveIdentity, proc_macros::DeriveIdentity)]
struct S;
"#,
        );
        let index = twin_index(&db, normal, test);
        assert!(index.unmatched.is_empty());
        let generated: Vec<_> = index
            .twins
            .keys()
            .filter(|&&item| ast_id(&db, item).unwrap().file_id.is_macro())
            .collect();
        assert_eq!(generated.len(), 3);
        for &&item in &generated {
            assert!(!reads(&db, item).unknown);
        }
        assert_eq!(index.function_bodies.unknown, 0);
        assert_eq!(index.function_bodies.twins, 2);
        assert_eq!(index.unknown, 0);
    }

    #[test]
    fn resolved_default_helper_is_not_unknown() {
        let (db, normal, test) = pair(
            r#"
//- minicore: derive, default
//- /lib.rs crate:main
#[derive(Default)]
enum Choice { #[default] First, Second }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.unknown, 0);
        assert_eq!(index.cfg_differing, 0);
        assert!(index.unmatched.is_empty());
    }

    #[test]
    fn unresolved_helper_spelling_stays_unknown() {
        let (db, normal, test) = pair(
            r#"
enum Choice { #[default] First, Second }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.unknown, 2);
    }

    #[test]
    fn different_actual_derive_outputs_are_unmatched() {
        let (db, normal, test) = pair(
            r#"
//- proc_macros: derive_identity
//- minicore: derive
//- /lib.rs crate:main
#[derive(proc_macros::DeriveIdentity)]
struct S { #[cfg(test)] field: u8 }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 1);
        assert_eq!(index.unmatched.len(), 1);
        assert_eq!(index.cfg_differing, 1);
    }

    #[test]
    fn generated_test_only_and_module_gates() {
        let (db, normal, test) = pair(
            r#"
//- /lib.rs crate:main
macro_rules! make { () => { #[cfg(test)] fn only() {} fn shared() {} } }
make!();
#[cfg(test)] mod tests;
#[test] fn test() {}
//- /tests.rs
fn nested() {}
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.test_only.len(), 4);
        assert_eq!(index.function_bodies.test_only, 3);
        assert!(index.unmatched.is_empty());
        assert_eq!(index.twins.len(), 1);
    }

    #[test]
    fn tls_attribute_is_known_but_cfg_attr_is_observed() {
        let (db, normal, test) = pair(
            r#"
#[thread_local] static STATE: u8 = 0;
#[cfg_attr(test, thread_local)] static SWITCH: u8 = 0;
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 2);
        assert_eq!(index.unknown, 0);
        assert_eq!(index.cfg_differing, 1);
    }

    #[test]
    fn private_macro_definitions_have_ancestor_gates() {
        let (db, normal, test) = pair(
            r#"
macro_rules! common { () => { () } }
#[cfg(test)] mod tests {
    macro_rules! private { () => { () } }
}
"#,
        );
        let definitions = &crate_items(&db, test).definitions;
        assert_eq!(definitions.len(), 2);
        let disabled = definitions
            .values()
            .filter(|&&item| gated_off(&db, item, normal.cfg_options(&db)))
            .count();
        assert_eq!(disabled, 1);
    }

    #[test]
    fn crate_hygiene_and_macro_definition_cfg() {
        let (db, normal, test) = pair(
            r#"
fn helper() {}
macro_rules! make { () => { fn generated() { $crate::helper(); } } }
make!();
#[cfg_attr(test, allow(dead_code))]
macro_rules! configured { () => { 0 } }
fn uncertain() { configured!(); }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 3);
        assert_eq!(index.unknown, 1);
        assert!(index.unmatched.is_empty());
    }

    #[test]
    fn different_actual_body_outputs_are_unknown() {
        use salsa::Setter;
        let (mut db, normal, test) = pair(
            r#"
//- minicore: env
//- /lib.rs crate:main
fn environment() { env!("TWIN_VALUE"); }
"#,
        );
        let mut env = normal.env(&db).clone();
        env.set("TWIN_VALUE", "normal");
        normal.set_env(&mut db).to(env.clone());
        env.set("TWIN_VALUE", "test");
        test.set_env(&mut db).to(env);
        let index = twin_index(&db, normal, test);
        assert_eq!(index.twins.len(), 1);
        assert_eq!(index.cfg_differing, 0);
        assert_eq!(index.unknown, 1);
    }

    #[test]
    fn items_in_expression_expansions() {
        let (db, normal, test) = pair(
            r#"
macro_rules! expression { () => {{ fn nested() {} const VALUE: u8 = 0; VALUE }} }
macro_rules! empty { () => {} }
fn expanded() { expression!(); }
fn empty_body() { empty!(); }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.function_bodies.twins, 3);
        assert!(index.unmatched.is_empty());
        assert_eq!(index.unknown, 0);
    }

    #[test]
    fn source_items_in_different_module_expansions() {
        let (db, normal, test) = pair(
            r#"
//- proc_macros: identity
//- /lib.rs crate:main
#[proc_macros::identity]
#[cfg_attr(test, allow(dead_code))]
mod generated { mod outside; #[cfg(test)] fn only() {} }
//- /generated/outside.rs
fn source() {}
"#,
        );
        let index = twin_index(&db, normal, test);
        assert_eq!(index.function_bodies.unmatched, 1);
        assert_eq!(index.function_bodies.test_only, 1);
        assert_eq!(index.function_bodies.twins, 0);
    }
}
