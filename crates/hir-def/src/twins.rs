//! Source twins and cfg observations; neither implies semantic equivalence.
//!
//! Rustc's `StripUnconfigured::{configure, process_cfg_attrs, configure_expr}` in
//! <https://github.com/rust-lang/rust/blob/1.93.0/compiler/rustc_expand/src/config.rs>
//! processes cfg_attr before gates and strips disabled nodes before their children.
//! These observations preserve RA's evaluation and include ancestor decisions;
//! opaque macro inputs are unknown rather than assumed independent of cfg.

use std::ops::ControlFlow;

use base_db::{Crate, SourceDatabase};
use cfg::{CfgOptions, CfgReads};
use hir_expand::{ErasedAstId, attrs::expand_cfg_attr};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::{AstNode, SyntaxNode, ast};

use crate::{
    AdtId, AttrDefId, DefWithBodyId, HasModule, Lookup, MacroId, ModuleDefId,
    attrs::AttrFlags,
    expr_store::Body,
    item_scope::ItemScope,
    nameres::{DefMap, crate_def_map},
};

fn ast_id(db: &dyn SourceDatabase, item: AttrDefId) -> Option<ErasedAstId> {
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
                            | "deprecated"
                            | "non_exhaustive"
                            | "automatically_derived"
                            | "unsafe"
                    )
                }) {
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
    if let Some(attrs) = crate::attrs::parse_extra_crate_attrs(db, krate) {
        observe_attrs(&ast::AnyHasAttrs::new(attrs), &options, &mut reads);
    }
    let Some(id) = ast_id(db, item) else {
        reads.unknown = true;
        return reads;
    };
    if id.file_id.is_macro() {
        reads.unknown = true;
        return reads;
    }
    let syntax = node(db, id);
    if let Some(recorded) =
        crate::item_tree::file_item_tree(db, id.file_id, krate).cfg_reads.get(&id.value)
    {
        reads.merge(recorded);
    }
    for ancestor in syntax.ancestors() {
        if let Some(owner) = ast::AnyHasAttrs::cast(ancestor) {
            observe_attrs(&owner, &options, &mut reads);
        }
    }
    let mut module = Some(item.module(db));
    while let Some(id) = module {
        let data = id.def_map(db).module(db, id);
        if let Some(source) = data.declaration_source(db) {
            for ancestor in source.value.syntax().ancestors() {
                if let Some(owner) = ast::AnyHasAttrs::cast(ancestor) {
                    observe_attrs(&owner, &options, &mut reads);
                }
            }
        }
        let source = data.definition_source(db);
        if let crate::nameres::ModuleSource::SourceFile(file) = source.value {
            observe_attrs(&ast::AnyHasAttrs::new(file), &options, &mut reads);
        }
        module = id.containing_module(db);
    }
    // Bodies and nested items have their own observations.
    let mut walk = syntax.preorder();
    while let Some(event) = walk.next() {
        if let syntax::WalkEvent::Enter(child) = event {
            if child != syntax
                && (ast::Item::can_cast(child.kind()) || ast::BlockExpr::can_cast(child.kind()))
            {
                walk.skip_subtree();
            } else if child != syntax
                && let Some(owner) = ast::AnyHasAttrs::cast(child)
                && !observe_attrs(&owner, &options, &mut reads)
            {
                walk.skip_subtree();
            }
        }
    }
    reads.merge(&recorder.finish());
    reads
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct SourceKey {
    id: ErasedAstId,
    containers: Vec<ErasedAstId>,
}

fn source_key(db: &dyn SourceDatabase, item: AttrDefId) -> Option<SourceKey> {
    let id = ast_id(db, item)?;
    if id.file_id.is_macro() {
        return None;
    }
    let syntax = node(db, id);
    let map = id.file_id.ast_id_map(db);
    let mut containers: Vec<_> = syntax
        .ancestors()
        .skip(1)
        .filter_map(ast::Item::cast)
        .map(|item| hir_expand::AstId::new(id.file_id, map.ast_id(&item)).erase())
        .collect();
    let mut module = Some(item.module(db));
    while let Some(id) = module {
        let data = id.def_map(db).module(db, id);
        if let Some(declaration) = data.origin.declaration() {
            if declaration.file_id.is_macro() {
                return None;
            }
            containers.push(declaration.erase());
        }
        module = id.containing_module(db);
    }
    Some(SourceKey { id, containers })
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct TwinIndex {
    /// T to N. These are source matches, not a shareable set.
    pub twins: FxHashMap<AttrDefId, AttrDefId>,
    pub unmatched: FxHashSet<AttrDefId>,
    pub normal_only: usize,
    pub cfg_differing: usize,
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

fn collect(db: &dyn SourceDatabase, map: &DefMap, items: &mut FxHashSet<AttrDefId>) {
    for (_, module) in map.modules(db) {
        scope_items(db, module.scope(db), items);
    }
}

fn crate_items(db: &dyn SourceDatabase, krate: Crate) -> FxHashSet<AttrDefId> {
    let mut items = FxHashSet::default();
    collect(db, crate_def_map(db, krate), &mut items);
    let mut seen = FxHashSet::default();
    loop {
        let pending: Vec<_> =
            items.iter().copied().filter_map(body).filter(|item| seen.insert(*item)).collect();
        if pending.is_empty() {
            break;
        }
        for owner in pending {
            for (_, map) in Body::of(db, owner).blocks(db) {
                collect(db, map, &mut items);
            }
        }
    }
    items
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
    let mut by_source = FxHashMap::default();
    for &item in &normal_items {
        if let Some(key) = source_key(db, item) {
            by_source.entry(key).or_insert_with(Vec::new).push(item);
        }
    }
    let mut matched = FxHashSet::default();
    for item in crate_items(db, test) {
        let twin = source_key(db, item)
            .and_then(|key| by_source.get(&key))
            .filter(|items| items.len() == 1)
            .map(|items| items[0]);
        let Some(twin) = twin else {
            result.unmatched.insert(item);
            continue;
        };
        matched.insert(twin);
        result.twins.insert(item, twin);
        let (n, t) = (reads(db, twin), reads(db, item));
        result.cfg_differing += usize::from(
            n.differs_from(test.cfg_options(db)) || t.differs_from(normal.cfg_options(db)),
        );
        result.unknown += usize::from(n.unknown || t.unknown);
    }
    result.normal_only = normal_items.len() - matched.len();
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
        assert_eq!(index.unmatched.len(), 1);
        assert_eq!(index.normal_only, 1);
        assert_eq!(index.unknown, 0);
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
        assert_eq!(reads.atoms.len(), 1);
        assert!(
            !reads.atoms
                [&cfg::CfgAtom::KeyValue { key: sym::feature, value: intern::Symbol::intern("x") }]
        );
        assert!(!reads.atoms.contains_key(&cfg::CfgAtom::Flag(sym::test)));
    }

    #[test]
    fn generated_and_uncertain_items() {
        let (db, normal, test) = pair(
            r#"
macro_rules! make { () => { fn generated() {} } }
make!();
fn unresolved() { missing!(); }
#[cfg()] fn malformed() {}
fn malformed_body() { #[cfg()] let _ = 0; }
fn opaque_body() { #[magic] let _ = 0; }
"#,
        );
        let index = twin_index(&db, normal, test);
        assert!(!index.unmatched.is_empty());
        assert_eq!(index.cfg_differing, 0);
        assert_eq!(index.unknown, 4);
        assert!(index.twins.iter().all(|(t, n)| !ast_id(&db, *t).unwrap().file_id.is_macro()
            && !ast_id(&db, *n).unwrap().file_id.is_macro()));
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
        assert_eq!(index.unmatched.len(), 1);
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
}
