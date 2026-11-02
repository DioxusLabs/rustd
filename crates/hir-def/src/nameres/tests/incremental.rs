use base_db::{
    CrateDisplayName, CrateGraphBuilder, CrateName, CrateOrigin, CrateWorkspaceData,
    DependencyBuilder, Env, SourceDatabase, all_crates,
};
use expect_test::{Expect, expect};
use intern::Symbol;
use span::Edition;
use test_fixture::WithFixture;
use triomphe::Arc;

use crate::{
    file_item_tree,
    nameres::{crate_def_map, tests::TestDB},
};

#[test]
fn lru_capacity_retention() {
    use salsa::{Database, Durability};

    for capacity in [None, Some(1), Some(0)] {
        let (mut db, files) = TestDB::with_many_files(
            r#"
//- /lib.rs
fn f() {}
//- /empty.rs
//- /broken.rs
fn {
"#,
        );
        if let Some(capacity) = capacity {
            crate::set_lru_capacity(&mut db, capacity);
        }
        let read = |db: &TestDB| {
            files.iter().map(|&file| {
                let parse = file.parse(db);
                hir_expand::HirFileId::from(file).ast_id_map(db);
                (parse.syntax_node().text().to_string(), parse.errors().len())
            }).collect::<Vec<_>>()
        };
        let expected = read(&db);
        assert_eq!(expected[1], (String::new(), 0));
        assert!(expected[2].1 > 0);
        db.synthetic_write(Durability::HIGH);
        let executed = db.log_executed(|| assert_eq!(read(&db), expected));
        let parses = executed.iter().filter(|name| name.as_str() == "EditionedFileId::parse_").count();
        if capacity == Some(1) {
            assert!(parses > 0, "{executed:?}");
        } else {
            assert_eq!(parses, 0, "{executed:?}");
        }
    }
}

#[test]
fn body_inventory_ignores_source_offset_changes() {
    let (mut db, files) = TestDB::with_many_files(
        r#"
//- /lib.rs
macro_rules! call { () => { () }; }
fn edited() { let enabled = true; let _ = enabled; }
fn later() {
    call!(); call!(); call!(); call!(); call!(); call!();
    { struct Local; }
    { struct Other; }
}
fn empty() {}
fn unresolved() { missing!(); }
"#,
    );
    let krate = db.fetch_test_crate();
    crate::twins::crate_items(&db, krate);
    let file = files[0].file_id(&db);
    let original = db.file_text(file).text(&db).clone();
    for spaces in 1..=32 {
        let text = original.replace("= enabled", &format!("={}enabled", " ".repeat(spaces + 1)));
        db.set_file_text(file, &text);
        let executed = db.log_executed(|| {
            crate::twins::crate_items(&db, krate);
        });
        assert!(executed.iter().any(|name| name == "body_inventory"), "{executed:?}");
        assert!(!executed.iter().any(|name| name == "crate_items"), "{executed:?}");
    }
}

#[test]
fn def_map_laundered_macro_frontier_validation() {
    use crate::item_tree::{file_item_tree_snapshot, inputs::ItemTreeInput};
    use salsa::{Durability, Setter};

    let fixture = r#"
//- proc_macros: identity, mirror, derive_identity
//- /lib.rs
mod a;
mod b;
//- /a.rs
fn edited() { let _ = 0; }
macro_rules! make { () => { pub struct Generated; } }
make!();
#[proc_macros::identity]
#[derive(proc_macros::DeriveIdentity)]
pub struct Derived;
proc_macros::mirror! { pub struct Mirrored; }
//- /b.rs
pub struct Other;
impl Other { pub fn f() {} }
proc_macros::mirror! { pub struct Unselected; }
"#;
    let mut counts = Vec::new();
    for launder in [false, true] {
        let (mut db, files) = TestDB::with_many_files(fixture);
        let krate = db.fetch_test_crate();
        assert_eq!(krate.root_file_id(&db), files[0]);
        let edited = files[1];
        let roots: std::collections::HashSet<_> = all_crates(&db)
            .iter()
            .map(|&krate| {
                db.file_source_root(krate.root_file_id(&db).file_id(&db)).source_root_id(&db)
            })
            .collect();
        for root in roots {
            let source = db.source_root(root).source_root(&db);
            let durability = if source.is_library { Durability::HIGH } else { Durability::MEDIUM };
            for file in source.iter() {
                let text = db.file_text(file).text(&db).clone();
                db.set_file_text_with_durability(file, &text, durability);
                db.set_file_source_root_with_durability(file, root, durability);
            }
            db.set_source_root_with_durability(root, source, durability);
        }
        for &file in &files {
            let text = db.file_text(file.file_id(&db)).text(&db).clone();
            db.set_file_text_with_durability(file.file_id(&db), &text, Durability::MEDIUM);
        }
        if launder {
            db.macro_expansions = Some(Default::default());
            db.macro_expansions.as_ref().unwrap().select_file(edited.file_id(&db));
            db.macro_expansions.as_ref().unwrap().set_collecting(true);
            for &file in &files {
                let value = file_item_tree_snapshot(&db, file.into(), krate);
                let input = ItemTreeInput::builder(value).durability(Durability::MEDIUM).new(&db);
                db.item_trees.insert(file.into(), krate, input);
            }
        }
        let request = |db: &TestDB| {
            let map = crate_def_map(db, krate);
            for (_, module) in map.modules(db) {
                for id in module.scope(db).inherent_impls() {
                    crate::nameres::assoc::ImplItems::of(db, id);
                }
            }
        };
        request(&db);
        if let Some(inputs) = db.macro_expansions.clone() {
            assert!(!inputs.entries().is_empty());
            assert!(inputs.entries_for_file(files[2].file_id(&db)).is_empty());
            assert_eq!(inputs.entries_for_file(edited.file_id(&db)).len(), inputs.entry_count());
            for (call, input) in inputs.entries() {
                let value = call.parse_macro_expansion(&db).clone();
                input.set_value(&mut db).with_durability(Durability::MEDIUM).to(Some(value));
            }
            request(&db);
            inputs.set_collecting(false);
        }
        let old = db.file_text(edited.file_id(&db)).text(&db).clone();
        assert!(old.contains("fn edited()"), "wrong edited file: {old}");
        for edit in [1, 2] {
            db.set_file_text_with_durability(
                edited.file_id(&db),
                &old.replace("= 0;", &format!("= {edit};")),
                Durability::LOW,
            );
            if launder {
                let input = db.item_trees.get(edited.into(), krate).unwrap();
                assert_eq!(*input.value(&db), file_item_tree_snapshot(&db, edited.into(), krate));
                for (call, input) in db.macro_expansions.as_ref().unwrap().entries() {
                    let value = call.parse_macro_expansion(&db).clone();
                    if input.value(&db).as_ref() != Some(&value) {
                        input
                            .set_value(&mut db)
                            .with_durability(Durability::MEDIUM)
                            .to(Some(value));
                    }
                }
            }
            let mut events = db.log(|| {
                crate_def_map(&db, krate);
            });
            let def_map_validations = events
                .iter()
                .filter(|event| {
                    matches!(event.kind, salsa::EventKind::DidValidateMemoizedValue { .. })
                })
                .count();
            eprintln!(
                "frontier launder={launder} edit={edit}: def-map validations={def_map_validations}"
            );
            events.extend(db.log(|| request(&db)));
            let mut validations = std::collections::BTreeMap::<String, usize>::new();
            let mut executions = std::collections::BTreeMap::<String, usize>::new();
            for event in &events {
                match event.kind {
                    salsa::EventKind::DidValidateMemoizedValue { database_key } => {
                        let name = salsa::Database::ingredient_debug_name(
                            &db,
                            database_key.ingredient_index(),
                        );
                        *validations.entry(name.into_owned()).or_default() += 1;
                    }
                    salsa::EventKind::WillExecute { database_key } => {
                        let name = salsa::Database::ingredient_debug_name(
                            &db,
                            database_key.ingredient_index(),
                        );
                        *executions.entry(name.into_owned()).or_default() += 1;
                        if edit == 2 {
                            assert_ne!(
                                salsa::Database::ingredient_debug_name(
                                    &db,
                                    database_key.ingredient_index(),
                                ),
                                "crate_local_def_map"
                            );
                        }
                    }
                    _ => {}
                }
            }
            let count = validations.values().sum::<usize>();
            eprintln!("frontier launder={launder}: validations={count} {validations:?}");
            eprintln!("frontier launder={launder}: executions={executions:?}");
            if edit == 2 {
                counts.push(count);
            }
        }
    }
    assert!(counts[1] < counts[0], "frontier/control: {counts:?}");
    assert!(counts[1] <= 16, "frontier still leaks: {counts:?}");
}

fn check_def_map_is_not_recomputed(
    #[rust_analyzer::rust_fixture] ra_fixture_initial: &str,
    #[rust_analyzer::rust_fixture] ra_fixture_change: &str,
    expecta: Expect,
    expectb: Expect,
) {
    let (mut db, pos) = TestDB::with_position(ra_fixture_initial);
    let krate = db.fetch_test_crate();
    execute_assert_events(
        &db,
        || {
            crate_def_map(&db, krate);
        },
        &[],
        expecta,
    );
    db.set_file_text(pos.file_id.file_id(&db), ra_fixture_change);

    execute_assert_events(
        &db,
        || {
            crate_def_map(&db, krate);
        },
        &[("crate_local_def_map", 0)],
        expectb,
    );
}

#[test]
fn crate_metadata_changes_should_not_invalidate_unrelated_def_maps() {
    let (mut db, files) = TestDB::with_many_files(
        r#"
//- /a.rs crate:a
pub fn foo() {}

//- /b.rs crate:b
pub struct Bar;

//- /c.rs crate:c deps:b
pub const BAZ: u32 = 0;
    "#,
    );

    for &krate in all_crates(&db).iter() {
        crate_def_map(&db, krate);
    }

    let all_crates_before = all_crates(&db);

    {
        // Add dependencies: c -> b, b -> a.
        let mut new_crate_graph = CrateGraphBuilder::default();

        let mut add_crate = |crate_name, root_file_idx: usize| {
            new_crate_graph.add_crate_root(
                files[root_file_idx].file_id(&db),
                Edition::CURRENT,
                Some(CrateDisplayName::from_canonical_name(crate_name)),
                None,
                Default::default(),
                None,
                Env::default(),
                CrateOrigin::Local { repo: None, name: Some(Symbol::intern(crate_name)) },
                Vec::new(),
                false,
                Arc::new(
                    // FIXME: This is less than ideal
                    TryFrom::try_from(
                        &*std::env::current_dir().unwrap().as_path().to_string_lossy(),
                    )
                    .unwrap(),
                ),
                Arc::new(CrateWorkspaceData { target: Err("".into()), toolchain: None }),
            )
        };
        let a = add_crate("a", 0);
        let b = add_crate("b", 1);
        let c = add_crate("c", 2);
        new_crate_graph
            .add_dep(c, DependencyBuilder::new(CrateName::new("b").unwrap(), b))
            .unwrap();
        new_crate_graph
            .add_dep(b, DependencyBuilder::new(CrateName::new("a").unwrap(), a))
            .unwrap();
        new_crate_graph.set_in_db(&mut db);
    }

    let all_crates_after = all_crates(&db);
    assert!(
        std::sync::Arc::ptr_eq(&all_crates_before, &all_crates_after),
        "the all_crates list should not have been invalidated"
    );
    execute_assert_events(
        &db,
        || {
            for &krate in all_crates(&db).iter() {
                crate_def_map(&db, krate);
            }
        },
        // `c` gets invalidated as its dependency `b` changed
        // `b` gets invalidated due to its new dependency edge to `a`
        &[("crate_local_def_map", 2)],
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "crate_local_def_map",
            ]
        "#]],
    );
}

#[test]
fn typing_inside_a_function_should_not_invalidate_def_map() {
    check_def_map_is_not_recomputed(
        r"
//- /lib.rs
mod foo;$0

use crate::foo::bar::Baz;

enum E { A, B }
use E::*;

fn foo() -> i32 {
    1 + 1
}

#[cfg(never)]
fn no() {}
//- /foo/mod.rs
pub mod bar;

//- /foo/bar.rs
pub struct Baz;
",
        r"
mod foo;

use crate::foo::bar::Baz;

enum E { A, B }
use E::*;

fn foo() -> i32 { 92 }

#[cfg(never)]
fn no() {}
",
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "EnumVariants::of_",
            ]
        "#]],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
                "EnumVariants::of_",
            ]
        "#]],
    );
}

#[test]
fn typing_inside_a_macro_should_not_invalidate_def_map() {
    check_def_map_is_not_recomputed(
        r"
//- /lib.rs
macro_rules! m {
    ($ident:ident) => {
        fn f() {
            $ident + $ident;
        };
    }
}
mod foo;

//- /foo/mod.rs
pub mod bar;

//- /foo/bar.rs
$0
m!(X);

pub struct S {}
",
        r"
m!(Y);

pub struct S {}
",
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "AstId < ast :: Macro >::decl_macro_expander_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
            ]
        "#]],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
                "MacroCallId::macro_arg_",
                "MacroCallId::parse_macro_expansion_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
            ]
        "#]],
    );
}

#[test]
fn typing_inside_an_attribute_should_not_invalidate_def_map() {
    check_def_map_is_not_recomputed(
        r"
//- proc_macros: identity
//- /lib.rs
mod foo;

//- /foo/mod.rs
pub mod bar;

//- /foo/bar.rs
$0
#[proc_macros::identity]
fn f() {}
",
        r"
#[proc_macros::identity]
fn f() { foo }
",
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "crate_local_def_map",
                "ProcMacros::get_for_crate_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "Modules < 'db >::module_",
                "ModuleScope < 'db >::name_",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::expand_proc_macro_",
                "MacroCallId::macro_arg_",
                "proc_macro_span",
            ]
        "#]],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
                "MacroCallId::macro_arg_",
                "MacroCallId::expand_proc_macro_",
                "MacroCallId::parse_macro_expansion_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
            ]
        "#]],
    );
}

// Would be nice if this was the case, but as attribute inputs are stored in the item tree, this is
// not currently the case.
// #[test]
// fn typing_inside_an_attribute_arg_should_not_invalidate_def_map() {
//     check_def_map_is_not_recomputed(
//         r"
// //- proc_macros: identity
// //- /lib.rs
// mod foo;

// //- /foo/mod.rs
// pub mod bar;

// //- /foo/bar.rs
// $0
// #[proc_macros::identity]
// fn f() {}
// ",
//         r"
// #[proc_macros::identity(foo)]
// fn f() {}
// ",
//     );
// }

#[test]
fn typing_inside_macro_heavy_file_should_not_invalidate_def_map() {
    check_def_map_is_not_recomputed(
        r"
//- proc_macros: identity, derive_identity
//- /lib.rs
macro_rules! m {
    ($ident:ident) => {
        fn fm() {
            $ident + $ident;
        };
    }
}
mod foo;

//- /foo/mod.rs
pub mod bar;

//- /foo/bar.rs
$0
fn f() {}

m!(X);
macro_rules! m2 {
    ($ident:ident) => {
        fn f2() {
            $ident + $ident;
        };
    }
}
m2!(X);

#[proc_macros::identity]
#[derive(proc_macros::DeriveIdentity)]
pub struct S {}
",
        r"
fn f() {0}

m!(X);
macro_rules! m2 {
    ($ident:ident) => {
        fn f2() {
            $ident + $ident;
        };
    }
}
m2!(X);

#[proc_macros::identity]
#[derive(proc_macros::DeriveIdentity)]
pub struct S {}
",
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "crate_local_def_map",
                "ProcMacros::get_for_crate_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "AstId < ast :: Macro >::decl_macro_expander_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
                "AstId < ast :: Macro >::decl_macro_expander_",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
                "Modules < 'db >::module_",
                "ModuleScope < 'db >::name_",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::expand_proc_macro_",
                "MacroCallId::macro_arg_",
                "proc_macro_span",
            ]
        "#]],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
                "MacroCallId::macro_arg_",
                "AstId < ast :: Macro >::decl_macro_expander_",
                "MacroCallId::macro_arg_",
                "MacroCallId::macro_arg_",
            ]
        "#]],
    );
}

// Would be nice if this was the case, but as attribute inputs are stored in the item tree, this is
// not currently the case.
// #[test]
// fn typing_inside_a_derive_should_not_invalidate_def_map() {
//     check_def_map_is_not_recomputed(
//         r"
// //- proc_macros: derive_identity
// //- minicore:derive
// //- /lib.rs
// mod foo;

// //- /foo/mod.rs
// pub mod bar;

// //- /foo/bar.rs
// $0
// #[derive(proc_macros::DeriveIdentity)]
// #[allow()]
// struct S;
// ",
//         r"
// #[derive(proc_macros::DeriveIdentity)]
// #[allow(dead_code)]
// struct S;
// ",
//     );
// }

#[test]
fn typing_inside_a_function_should_not_invalidate_item_expansions() {
    let (mut db, pos) = TestDB::with_position(
        r#"
//- /lib.rs
macro_rules! m {
    ($ident:ident) => {
        fn $ident() { };
    }
}
mod foo;

//- /foo/mod.rs
pub mod bar;

//- /foo/bar.rs
m!(X);
fn quux() { 1$0 }
m!(Y);
m!(Z);
"#,
    );
    let krate = db.test_crate();
    execute_assert_events(
        &db,
        || {
            let crate_def_map = crate_def_map(&db, krate);
            let module_data = &crate_def_map.module(
                &db,
                crate_def_map.modules_for_file(&db, pos.file_id.file_id(&db)).next().unwrap(),
            );
            assert_eq!(module_data.scope(&db).resolutions().count(), 4);
        },
        &[("file_item_tree_query", 6), ("parse_macro_expansion", 3)],
        expect![[r#"
            [
                "crate_local_def_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "AstId < ast :: Macro >::decl_macro_expander_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
                "MacroId::definition_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "MacroCallId::parse_macro_expansion_",
                "MacroCallId::macro_arg_",
                "Modules < 'db >::module_",
            ]
        "#]],
    );

    let new_text = r#"
m!(X);
fn quux() { 92 }
m!(Y);
m!(Z);
"#;
    db.set_file_text(pos.file_id.file_id(&db), new_text);

    execute_assert_events(
        &db,
        || {
            let crate_def_map = crate_def_map(&db, krate);
            let module_data = &crate_def_map.module(
                &db,
                crate_def_map.modules_for_file(&db, pos.file_id.file_id(&db)).next().unwrap(),
            );
            assert_eq!(module_data.scope(&db).resolutions().count(), 4);
        },
        &[("file_item_tree_query", 1), ("parse_macro_expansion", 0)],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
                "MacroCallId::macro_arg_",
                "MacroCallId::macro_arg_",
                "MacroCallId::macro_arg_",
            ]
        "#]],
    );
}

#[test]
fn item_tree_prevents_reparsing() {
    let (mut db, pos) = TestDB::with_position(
        r#"
pub struct S;
pub union U {}
pub enum E {
    Variant,
}
pub fn f(_: S) { $0 }
pub trait Tr {}
impl Tr for () {}
pub const C: u8 = 0;
pub static ST: u8 = 0;
pub type Ty = ();
"#,
    );

    execute_assert_events(
        &db,
        || {
            file_item_tree(&db, pos.file_id.into(), db.test_crate());
        },
        &[("file_item_tree_query", 1), ("parse", 1)],
        expect![[r#"
            [
                "file_item_tree_query",
                "HirFileId::ast_id_map_",
                "EditionedFileId::parse_",
                "real_span_map",
            ]
        "#]],
    );

    let file_id = pos.file_id.file_id(&db);
    let file_text = db.file_text(file_id).text(&db);
    db.set_file_text(file_id, &format!("{file_text}\n"));

    execute_assert_events(
        &db,
        || {
            file_item_tree(&db, pos.file_id.into(), db.test_crate());
        },
        &[("file_item_tree_query", 1), ("parse", 1)],
        expect![[r#"
            [
                "EditionedFileId::parse_",
                "HirFileId::ast_id_map_",
                "file_item_tree_query",
                "real_span_map",
            ]
        "#]],
    );
}

fn execute_assert_events(
    db: &TestDB,
    f: impl FnOnce(),
    required: &[(&str, usize)],
    expect: Expect,
) {
    let events = db.log_executed(f);
    for (event, count) in required {
        let n = events.iter().filter(|it| it.contains(event)).count();
        assert_eq!(n, *count, "Expected {event} to be executed {count} times, but only got {n}");
    }
    expect.assert_debug_eq(&events);
}

#[test]
fn item_after_impl_is_its_own_span_anchor() {
    use hir_expand::HirFileId;
    use syntax::{
        AstNode,
        ast::{self, HasModuleItem},
    };

    let (db, pos) = TestDB::with_position(
        r#"
struct S;
impl S {
    fn first(&self) {}
    fn last(&self) {$0}
}
struct AfterImpl;
"#,
    );
    let file_id = HirFileId::from(pos.file_id);
    let after_impl = pos.file_id.parse(&db).tree().items().last().unwrap();
    assert!(matches!(after_impl, ast::Item::Struct(_)));
    let span = file_id.span_map(&db).span_for_range(after_impl.syntax().text_range());

    assert_eq!(span.anchor.ast_id, file_id.ast_id_map(&db).ast_id(&after_impl).erase());
    assert_eq!(u32::from(span.range.start()), 0);
}
