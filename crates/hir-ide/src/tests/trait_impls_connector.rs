use base_db::{SourceDatabase, salsa::Durability};
use hir_ty::method_resolution::{InherentImpls, TraitImpls};
use test_fixture::WithFixture;

use crate::test_db::TestDB;

const PREFIX: &str = "trait T {} trait U {} struct S; macro_rules! m { () => { impl T for S {} } }";

fn source(body: &str) -> String {
    format!("{PREFIX} fn f() {{ {body} }} fn g() {{ let _ = 0; }}")
}

fn refresh(db: &mut TestDB, file: base_db::FileId, text: &str) {
    let inputs = db.trait_impls.clone();
    inputs.written(db, file, text);
    db.set_file_text_with_durability(file, text, Durability::LOW);
    let krate = db.test_crate();
    inputs.refresh(db, &[krate], true);
}

fn populate(db: &mut TestDB) {
    let krate = db.test_crate();
    let inputs = db.trait_impls.clone();
    inputs.refresh(db, &[krate], false);
    TraitImpls::for_crate(db, krate);
    InherentImpls::for_crate(db, krate);
    inputs.refresh(db, &[krate], true);
}

#[test]
fn connector_body_edits_and_restoration() {
    let initial = source("let _ = 0;");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    let inputs = db.trait_impls.clone();
    populate(&mut db);
    let input = inputs.get(db.test_crate()).unwrap();
    let initial_index = input.value(&db).clone();
    for body in [
        "let _ = 1;",
        "impl T for S {}",
        "{ impl T for S {} fn nested() { impl U for S {} } }",
        "{ impl T for S {} fn nested() { impl T for S {} } }",
        "use T as Alias; impl Alias for S {}",
        "use U as Alias; impl Alias for S {}",
        "macro_rules! local { () => { impl U for S {} } } local!();",
        "m!();",
        "",
        "let _ = 0;",
    ] {
        let before = inputs.refresh_counts();
        refresh(&mut db, file, &source(body));
        let after = inputs.refresh_counts();
        assert_eq!(after.0, before.0, "unexpected full refresh for {body}");
        assert_eq!(after.1, before.1 + 1, "expected exactly the edited holder");
    }
    assert_eq!(initial_index, *input.value(&db));
}

#[test]
fn connector_structural_and_expansion_fallbacks() {
    let initial = source("let _ = 0;");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    let inputs = db.trait_impls.clone();
    populate(&mut db);
    let fixtures = [
        format!("{initial} impl T for S {{}}"),
        initial.clone(),
        source("#[macro_export] macro_rules! exported { () => {} }"),
        source("include /* comment */ ! (\"missing.rs\");"),
        initial.replace("fn f()", "#[possible_attribute_macro] fn f()"),
        source("let _ = 1;").replace("fn f()", "#[possible_attribute_macro] fn f()"),
        initial.clone(),
        // Equal item trees and invocation arguments do not pin macro definitions.
        format!("{PREFIX} m!(); fn f() {{}}"),
        format!(
            "{} m!(); fn f() {{}}",
            PREFIX.replace("impl T for S {}", &" ".repeat("impl T for S {}".len()))
        ),
        initial.clone(),
        initial.replace("= 0;", "= 1;"),
    ];
    for text in fixtures {
        let before = inputs.refresh_counts();
        refresh(&mut db, file, &text);
        assert_eq!(inputs.refresh_counts().0, before.0 + 1, "expected full refresh for {text}");
    }
}

#[test]
fn connector_split_preserves_interleaved_order_and_derives() {
    let (mut db, _) = TestDB::with_single_file(
        r#"
//- minicore: derive, clone
trait T {}
#[derive(Clone)]
struct S;
impl T for S {}
impl S { fn a() {} }
fn outer() { impl T for S {} { impl T for S {} } fn inner() { impl T for S {} } }
macro_rules! m { () => { impl T for S {} } }
mod a { use super::*; impl T for S {} fn f() { m!(); } }
mod b { use super::*; impl T for S {} fn f() { impl T for S {} } }
mod c { use super::*; impl S { fn a() {} } fn f() { impl S { fn b() {} } } }
"#,
    );
    let krate = db.test_crate();
    populate(&mut db);
    assert_eq!(TraitImpls::for_crate_tracked(&db, krate), TraitImpls::for_crate(&db, krate));
    assert_eq!(InherentImpls::for_crate_tracked(&db, krate), InherentImpls::for_crate(&db, krate));
}

#[test]
fn connector_cold_readiness_and_deselection() {
    let initial = source("impl T for S {}");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    let krate = db.test_crate();
    let inputs = db.trait_impls.clone();
    inputs.refresh(&mut db, &[krate], true);
    let input = inputs.get(krate).unwrap();
    assert!(input.value(&db).is_none());
    assert!(input.inherent(&db).is_none());
    populate(&mut db);
    assert!(input.value(&db).is_some());
    assert!(input.inherent(&db).is_some());
    TraitImpls::for_crate(&db, krate);
    inputs.refresh(&mut db, &[], true);
    assert!(input.value(&db).is_none());
    assert!(input.inherent(&db).is_none());
    db.set_file_text_with_durability(file, &source("impl U for S {}"), Durability::LOW);
    assert_eq!(TraitImpls::for_crate(&db, krate), TraitImpls::for_crate_tracked(&db, krate));
    assert_eq!(InherentImpls::for_crate(&db, krate), InherentImpls::for_crate_tracked(&db, krate));
}

#[test]
fn connector_randomized_edits() {
    let initial = source("let _ = 0;");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    populate(&mut db);
    let bodies = [
        "",
        "let _ = 0;",
        "let _ = 1;",
        "impl T for S {}",
        "m!();",
        "{ fn nested() { impl U for S {} } }",
        "use T as Alias; impl Alias for S {}",
        "use U as Alias; impl Alias for S {}",
        "macro_rules! local { () => { impl U for S {} } } local!();",
        "#[macro_export] macro_rules! exported { () => {} }",
    ];
    let mut seed = 0x7e57_1a2bu64;
    for _ in 0..320 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let mut text = source(bodies[((seed >> 32) as usize) % bodies.len()]);
        if seed & 31 == 0 {
            text.push_str(" impl T for S {}");
        }
        if seed & 63 == 1 {
            text = text.replace("fn f()", "#[possible_attribute_macro] fn f()");
        }
        refresh(&mut db, file, &text);
    }
    refresh(&mut db, file, &initial);
}

#[test]
fn connector_attribute_macro_body_edit_falls_back() {
    let (mut db, file) = TestDB::with_single_file(
        r#"
//- proc_macros: identity
//- /main.rs crate:main
use proc_macros::identity;
trait T {} struct S;
#[identity]
fn f() { impl T for S {} let _ = 0; }
"#,
    );
    let file = file.file_id(&db);
    populate(&mut db);
    let inputs = db.trait_impls.clone();
    let text = db.file_text(file).text(&db).replace("let _ = 0", "let _ = 1");
    let before = inputs.refresh_counts();
    refresh(&mut db, file, &text);
    assert_eq!(inputs.refresh_counts().0, before.0 + 1);
}

#[test]
fn connector_nested_attribute_macro_body_edit_falls_back() {
    let (mut db, file) = TestDB::with_single_file(
        r#"
//- proc_macros: identity
//- /main.rs crate:main
use proc_macros::identity;
trait T {} struct S;
fn outer() {
    #[identity]
    fn inner() { impl T for S {} let _ = 0; }
}
"#,
    );
    let file = file.file_id(&db);
    populate(&mut db);
    let inputs = db.trait_impls.clone();
    let text = db.file_text(file).text(&db).replace("let _ = 0", "let _ = 1");
    let before = inputs.refresh_counts();
    refresh(&mut db, file, &text);
    assert_eq!(inputs.refresh_counts().0, before.0 + 1);
}

#[test]
fn connector_const_static_unicode_empty_and_error_edits() {
    let initial =
        "trait T {} struct S; const C: () = { let _ = 0; }; static V: () = { let _ = \"é\"; };";
    let (mut db, file) = TestDB::with_single_file(initial);
    let file = file.file_id(&db);
    populate(&mut db);
    let inputs = db.trait_impls.clone();
    let before = inputs.refresh_counts();
    let text = initial.replace("let _ = 0;", "impl T for S {}");
    refresh(&mut db, file, &text);
    refresh(&mut db, file, &text.replace('é', "ê"));
    assert_eq!(inputs.refresh_counts(), (before.0, before.1 + 2));
    let before = inputs.refresh_counts();
    refresh(&mut db, file, &text.replace('é', "ê"));
    assert_eq!(inputs.refresh_counts(), before);
    for text in ["fn f( {", "", initial] {
        refresh(&mut db, file, text);
    }
    let before = inputs.refresh_counts();
    base_db::salsa::Database::synthetic_write(&mut db, Durability::MEDIUM);
    populate(&mut db);
    assert_eq!(inputs.refresh_counts().0, before.0 + 1);
}

fn inherent_source(body: &str) -> String {
    format!(
        "struct S; struct V; macro_rules! i {{ () => {{ impl S {{ fn f() {{}} }} }} }} \
         fn outer() {{ {body} }} fn other() {{ let _ = 0; }}"
    )
}

#[test]
fn connector_inherent_edits_and_restoration() {
    let initial = inherent_source("let _ = 0;");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    populate(&mut db);
    let inputs = db.trait_impls.clone();
    let input = inputs.get(db.test_crate()).unwrap();
    let empty = input.inherent(&db).clone();
    for body in [
        "let _ = 1;",
        "impl S { fn f() {} }",
        "impl V { fn f() {} }",
        "{ impl S { fn f() {} } fn nested() { impl V { fn g() {} } } }",
        "{ impl S { fn f() {} } fn nested() { impl S { fn g() {} } } }",
        "use S as Alias; impl Alias { fn f() {} }",
        "use V as Alias; impl Alias { fn f() {} }",
        "macro_rules! local { () => { impl V { fn f() {} } } } local!();",
        "i!();",
        "",
        "let _ = 0;",
    ] {
        let before = inputs.refresh_counts();
        refresh(&mut db, file, &inherent_source(body));
        assert_eq!(inputs.refresh_counts(), (before.0, before.1 + 1));
        assert_eq!(input.inherent(&db) == &empty, !body.contains("impl") && body != "i!();");
    }
    assert_eq!(*input.inherent(&db), empty);
    for text in [
        format!("{initial} impl S {{ fn f() {{}} }}"),
        initial.clone(),
        inherent_source("#[macro_export] macro_rules! exported { () => {} }"),
        inherent_source("impl S { fn f() {} }")
            .replace("fn outer()", "#[possible_macro] fn outer()"),
        "fn f( {".to_owned(),
        String::new(),
        initial,
    ] {
        let before = inputs.refresh_counts();
        refresh(&mut db, file, &text);
        assert_eq!(inputs.refresh_counts().0, before.0 + 1);
    }
    assert_eq!(*input.inherent(&db), empty);
}

#[test]
fn connector_inherent_randomized_edits() {
    let initial = inherent_source("");
    let (mut db, file) = TestDB::with_single_file(&initial);
    let file = file.file_id(&db);
    populate(&mut db);
    let bodies = [
        "",
        "let _ = 1;",
        "impl S { fn f() {} }",
        "impl V { fn f() {} }",
        "i!();",
        "{ fn nested() { impl V { fn f() {} } } }",
        "use S as Alias; impl Alias { fn f() {} }",
        "use V as Alias; impl Alias { fn f() {} }",
        "macro_rules! local { () => { impl V { fn f() {} } } } local!();",
        "#[macro_export] macro_rules! exported { () => {} }",
    ];
    let mut seed = 0x1a2b_7e57u64;
    for _ in 0..320 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let mut text = inherent_source(bodies[((seed >> 32) as usize) % bodies.len()]);
        if seed & 31 == 0 {
            text.push_str(" impl V { fn f() {} }");
        }
        if seed & 63 == 1 {
            text = text.replace("fn outer()", "#[possible_macro] fn outer()");
        }
        refresh(&mut db, file, &text);
    }
    refresh(&mut db, file, &initial);
}
