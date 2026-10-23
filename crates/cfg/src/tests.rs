use arbitrary::{Arbitrary, Unstructured};
use expect_test::{Expect, expect};
use intern::Symbol;
use syntax::{AstNode, Edition, ast};
use syntax_bridge::{
    DocCommentDesugarMode,
    dummy_test_span_utils::{DUMMY, DummyTestSpanMap},
    syntax_node_to_token_tree,
};

use crate::{CfgAtom, CfgExpr, CfgOptions, DnfExpr};

#[test]
fn cfg_read_recording() {
    let options = CfgOptions::default();
    let (recorded, reads) = options.recording();
    let test = CfgAtom::Flag(Symbol::intern("test"));
    let feature = CfgAtom::KeyValue { key: Symbol::intern("feature"), value: Symbol::intern("x") };
    assert_eq!(recorded, options);
    assert_eq!(
        recorded.check(&CfgExpr::All(Box::new([
            CfgExpr::Atom(test.clone()),
            CfgExpr::Atom(feature.clone())
        ]))),
        Some(false)
    );
    assert!(reads.finish().atoms.is_empty());
    assert_eq!(reads.finish().predicates.len(), 1);
    let mut changed = options.clone();
    changed.insert_atom(Symbol::intern("test"));
    changed.insert_key_value(Symbol::intern("feature"), Symbol::intern("x"));
    assert!(!reads.finish().agrees_with(&changed));
    assert!(!recorded.check_atom(&feature));
    assert!(!reads.finish().atoms[&feature]);
    assert!(!reads.finish().agrees_with(&changed));
    assert!(reads.finish().agrees_with(&options));
    let (_, empty) = options.recording();
    assert!(empty.finish().agrees_with(&changed));
    recorded.to_hashable();
    assert!(reads.finish().read_all.is_some());
    assert_eq!(recorded.check(&CfgExpr::Invalid), None);
    assert!(reads.finish().unknown);
    assert!(!reads.finish().agrees_with(&options));
    assert!(empty.finish().atoms.is_empty());
}

#[test]
fn predicate_results_and_diagnostics() {
    let mut options = CfgOptions::default();
    options.insert_key_value(Symbol::intern("feature"), Symbol::intern("x"));
    let (recorded, reads) = options.recording();
    let predicate = CfgExpr::Any(Box::new([
        CfgExpr::Atom(CfgAtom::Flag(Symbol::intern("test"))),
        CfgExpr::Atom(CfgAtom::KeyValue {
            key: Symbol::intern("feature"),
            value: Symbol::intern("x"),
        }),
    ]));
    assert_eq!(recorded.check(&predicate), Some(true));
    recorded.without_recording().to_hashable();
    assert!(reads.finish().read_all.is_none());
    let mut test = options.clone();
    test.insert_atom(Symbol::intern("test"));
    assert!(reads.finish().agrees_with(&test));
    assert!(!reads.finish().agrees_with(&CfgOptions::default()));
    assert!(reads.finish().atoms.is_empty());
}

#[track_caller]
fn parse_ast_cfg(pred: ast::CfgPredicate) -> CfgExpr {
    CfgExpr::parse_from_ast(pred)
}

#[track_caller]
fn assert_parse_result(input: &str, expected: CfgExpr) {
    let source_file = ast::SourceFile::parse(input, Edition::CURRENT).syntax_node();
    let pred_ast = source_file.descendants().find_map(ast::CfgPredicate::cast).unwrap();
    let tt = syntax_node_to_token_tree(
        pred_ast.syntax(),
        DummyTestSpanMap,
        DUMMY,
        DocCommentDesugarMode::ProcMacro,
    );
    let cfg = CfgExpr::parse(&tt);
    assert_eq!(cfg, expected);
    let cfg = parse_ast_cfg(pred_ast);
    assert_eq!(cfg, expected);
}

#[track_caller]
fn check_dnf(input: &str, expect: Expect) {
    let source_file = ast::SourceFile::parse(input, Edition::CURRENT).ok().unwrap();
    let pred_ast = source_file.syntax().descendants().find_map(ast::CfgPredicate::cast).unwrap();
    let tt = syntax_node_to_token_tree(
        pred_ast.syntax(),
        DummyTestSpanMap,
        DUMMY,
        DocCommentDesugarMode::ProcMacro,
    );
    let cfg = CfgExpr::parse(&tt);
    let actual = format!("#![cfg({})]", DnfExpr::new(&cfg));
    expect.assert_eq(&actual);
    let cfg = parse_ast_cfg(pred_ast);
    let actual = format!("#![cfg({})]", DnfExpr::new(&cfg));
    expect.assert_eq(&actual);
}

#[track_caller]
fn check_why_inactive(input: &str, opts: &CfgOptions, expect: Expect) {
    let source_file = ast::SourceFile::parse(input, Edition::CURRENT).ok().unwrap();
    let pred_ast = source_file.syntax().descendants().find_map(ast::CfgPredicate::cast).unwrap();
    let tt = syntax_node_to_token_tree(
        pred_ast.syntax(),
        DummyTestSpanMap,
        DUMMY,
        DocCommentDesugarMode::ProcMacro,
    );
    let cfg = CfgExpr::parse(&tt);
    let dnf = DnfExpr::new(&cfg);
    let why_inactive = dnf.why_inactive(opts).unwrap().to_string();
    expect.assert_eq(&why_inactive);
    let cfg = parse_ast_cfg(pred_ast);
    let dnf = DnfExpr::new(&cfg);
    let why_inactive = dnf.why_inactive(opts).unwrap().to_string();
    expect.assert_eq(&why_inactive);
}

#[track_caller]
fn check_enable_hints(input: &str, opts: &CfgOptions, expected_hints: &[&str]) {
    let source_file = ast::SourceFile::parse(input, Edition::CURRENT).ok().unwrap();
    let pred_ast = source_file.syntax().descendants().find_map(ast::CfgPredicate::cast).unwrap();
    let tt = syntax_node_to_token_tree(
        pred_ast.syntax(),
        DummyTestSpanMap,
        DUMMY,
        DocCommentDesugarMode::ProcMacro,
    );
    let cfg = CfgExpr::parse(&tt);
    let dnf = DnfExpr::new(&cfg);
    let hints = dnf.compute_enable_hints(opts).map(|diff| diff.to_string()).collect::<Vec<_>>();
    assert_eq!(hints, expected_hints);
    let cfg = parse_ast_cfg(pred_ast);
    let dnf = DnfExpr::new(&cfg);
    let hints = dnf.compute_enable_hints(opts).map(|diff| diff.to_string()).collect::<Vec<_>>();
    assert_eq!(hints, expected_hints);
}

#[test]
fn test_cfg_expr_parser() {
    assert_parse_result("#![cfg(foo)]", CfgAtom::Flag(Symbol::intern("foo")).into());
    assert_parse_result("#![cfg(foo,)]", CfgAtom::Flag(Symbol::intern("foo")).into());
    assert_parse_result(
        "#![cfg(not(foo))]",
        CfgExpr::Not(Box::new(CfgAtom::Flag(Symbol::intern("foo")).into())),
    );
    assert_parse_result("#![cfg(foo(bar))]", CfgExpr::Invalid);

    // Only take the first
    assert_parse_result(
        r#"#![cfg(foo, bar = "baz")]"#,
        CfgAtom::Flag(Symbol::intern("foo")).into(),
    );

    assert_parse_result(
        r#"#![cfg(all(foo, bar = "baz"))]"#,
        CfgExpr::All(
            vec![
                CfgAtom::Flag(Symbol::intern("foo")).into(),
                CfgAtom::KeyValue { key: Symbol::intern("bar"), value: Symbol::intern("baz") }
                    .into(),
            ]
            .into_boxed_slice(),
        ),
    );
}

#[test]
fn smoke() {
    check_dnf("#![cfg(test)]", expect![[r#"#![cfg(test)]"#]]);
    check_dnf("#![cfg(not(test))]", expect![[r#"#![cfg(not(test))]"#]]);
    check_dnf("#![cfg(not(not(test)))]", expect![[r#"#![cfg(test)]"#]]);

    check_dnf("#![cfg(all(a, b))]", expect![[r#"#![cfg(all(a, b))]"#]]);
    check_dnf("#![cfg(any(a, b))]", expect![[r#"#![cfg(any(a, b))]"#]]);

    check_dnf("#![cfg(not(a))]", expect![[r#"#![cfg(not(a))]"#]]);
}

#[test]
fn distribute() {
    check_dnf("#![cfg(all(any(a, b), c))]", expect![[r#"#![cfg(any(all(a, c), all(b, c)))]"#]]);
    check_dnf("#![cfg(all(c, any(a, b)))]", expect![[r#"#![cfg(any(all(c, a), all(c, b)))]"#]]);
    check_dnf(
        "#![cfg(all(any(a, b), any(c, d)))]",
        expect![[r#"#![cfg(any(all(a, c), all(a, d), all(b, c), all(b, d)))]"#]],
    );

    check_dnf(
        "#![cfg(all(any(a, b, c), any(d, e, f), g))]",
        expect![[
            r#"#![cfg(any(all(a, d, g), all(a, e, g), all(a, f, g), all(b, d, g), all(b, e, g), all(b, f, g), all(c, d, g), all(c, e, g), all(c, f, g)))]"#
        ]],
    );
}

#[test]
fn demorgan() {
    check_dnf("#![cfg(not(all(a, b)))]", expect![[r#"#![cfg(any(not(a), not(b)))]"#]]);
    check_dnf("#![cfg(not(any(a, b)))]", expect![[r#"#![cfg(all(not(a), not(b)))]"#]]);

    check_dnf("#![cfg(not(all(not(a), b)))]", expect![[r#"#![cfg(any(a, not(b)))]"#]]);
    check_dnf("#![cfg(not(any(a, not(b))))]", expect![[r#"#![cfg(all(not(a), b))]"#]]);
}

#[test]
fn nested() {
    check_dnf("#![cfg(all(any(a), not(all(any(b)))))]", expect![[r#"#![cfg(all(a, not(b)))]"#]]);

    check_dnf("#![cfg(any(any(a, b)))]", expect![[r#"#![cfg(any(a, b))]"#]]);
    check_dnf("#![cfg(not(any(any(a, b))))]", expect![[r#"#![cfg(all(not(a), not(b)))]"#]]);
    check_dnf("#![cfg(all(all(a, b)))]", expect![[r#"#![cfg(all(a, b))]"#]]);
    check_dnf("#![cfg(not(all(all(a, b))))]", expect![[r#"#![cfg(any(not(a), not(b)))]"#]]);
}

#[test]
fn regression() {
    check_dnf("#![cfg(all(not(not(any(any(any()))))))]", expect![[r##"#![cfg(any())]"##]]);
    check_dnf("#![cfg(all(any(all(any()))))]", expect![[r##"#![cfg(any())]"##]]);
    check_dnf("#![cfg(all(all(any())))]", expect![[r##"#![cfg(any())]"##]]);

    check_dnf("#![cfg(all(all(any(), x)))]", expect![[r##"#![cfg(any())]"##]]);
    check_dnf("#![cfg(all(all(any()), x))]", expect![[r##"#![cfg(any())]"##]]);
    check_dnf("#![cfg(all(all(any(x))))]", expect![[r##"#![cfg(x)]"##]]);
    check_dnf("#![cfg(all(all(any(x), x)))]", expect![[r##"#![cfg(all(x, x))]"##]]);
}

#[test]
fn hints() {
    let mut opts = CfgOptions::default();

    check_enable_hints("#![cfg(test)]", &opts, &["enable test"]);
    check_enable_hints("#![cfg(not(test))]", &opts, &[]);

    check_enable_hints("#![cfg(any(a, b))]", &opts, &["enable a", "enable b"]);
    check_enable_hints("#![cfg(any(b, a))]", &opts, &["enable b", "enable a"]);

    check_enable_hints("#![cfg(all(a, b))]", &opts, &["enable a and b"]);

    opts.insert_atom(Symbol::intern("test"));

    check_enable_hints("#![cfg(test)]", &opts, &[]);
    check_enable_hints("#![cfg(not(test))]", &opts, &["disable test"]);

    opts.insert_atom(Symbol::intern("a"));
    opts.insert_atom(Symbol::intern("b"));
    check_enable_hints("#![cfg(all(not(a), not(b)))]", &opts, &["disable a and b"]);
}

/// Tests that we don't suggest hints for cfgs that express an inconsistent formula.
#[test]
fn hints_impossible() {
    let mut opts = CfgOptions::default();

    check_enable_hints("#![cfg(all(test, not(test)))]", &opts, &[]);

    opts.insert_atom(Symbol::intern("test"));

    check_enable_hints("#![cfg(all(test, not(test)))]", &opts, &[]);
}

#[test]
fn why_inactive() {
    let mut opts = CfgOptions::default();
    opts.insert_atom(Symbol::intern("test"));
    opts.insert_atom(Symbol::intern("test2"));

    check_why_inactive("#![cfg(a)]", &opts, expect![["a is disabled"]]);
    check_why_inactive("#![cfg(not(test))]", &opts, expect![["test is enabled"]]);

    check_why_inactive(
        "#![cfg(all(not(test), not(test2)))]",
        &opts,
        expect![["test and test2 are enabled"]],
    );
    check_why_inactive("#![cfg(all(a, b))]", &opts, expect![["a and b are disabled"]]);
    check_why_inactive(
        "#![cfg(all(not(test), a))]",
        &opts,
        expect![["test is enabled and a is disabled"]],
    );
    check_why_inactive(
        "#![cfg(all(not(test), test2, a))]",
        &opts,
        expect![["test is enabled and a is disabled"]],
    );
    check_why_inactive(
        "#![cfg(all(not(test), not(test2), a))]",
        &opts,
        expect![["test and test2 are enabled and a is disabled"]],
    );
}

#[test]
fn proptest() {
    const REPEATS: usize = 512;

    let mut rng = oorandom::Rand32::new(123456789);
    let mut buf = Vec::new();
    for _ in 0..REPEATS {
        buf.clear();
        while buf.len() < 512 {
            buf.extend(rng.rand_u32().to_ne_bytes());
        }

        let mut u = Unstructured::new(&buf);
        let cfg = CfgExpr::arbitrary(&mut u).unwrap();
        DnfExpr::new(&cfg);
    }
}
