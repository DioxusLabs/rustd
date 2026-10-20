//! The examples in the documentation of the workspace's libraries, tested as `cargo test --doc`
//! tests them, with nothing of rustdoc's or of rustc's on the workspace's code. The examples of
//! a library are a crate of their own, `rust_out`, which rust-analyzer adds beside the library
//! when the file for it is in [`DIR`]. The daemon writes every example into that crate as a
//! module and builds it as it builds any program; the harness it writes for it runs one
//! example a process, and tells the client how the ones that do not run went.
//!
//! An example that only a crate of its own can be, one with `#![feature]` or that names
//! `crate::`, fails and says so: none is handed to rustdoc.

mod extract;
mod program;

use std::{
    io::Write as _,
    path::{Path, PathBuf},
    sync::Mutex,
    time::Instant,
};

use anyhow::Context as _;
use ide_db::{
    RootDatabase,
    base_db::{self, SourceDatabase},
};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use syntax::{
    AstNode, Edition, SyntaxKind, TextRange, TextSize,
    ast::{self, HasModuleItem as _},
};

use extract::Marks;
use program::{Frame, Program};

/// Where the crate of the examples of each package is, under the target directory, named
/// after the package.
pub(crate) const DIR: &str = "rustd/doctests";

/// What rustdoc names the program of an example, and rust-analyzer the crate of them.
const CRATE: &str = "rust_out";

/// What the function that runs an example is named, before the example's number.
const RUNNER: &str = "__rustd_doctest_";

/// Where the runners start in the text of a crate of examples, after every example.
const RUNNERS: &str = "// The examples that run.\n";

/// The code a test harness ends with when a test failed.
const FAILED: i32 = 101;

/// What each crate of examples was last written with, by its file.
static WRITTEN: Mutex<Option<FxHashMap<vfs::FileId, Vec<Entry>>>> = Mutex::new(None);

/// An example as the harness the daemon writes lists it.
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub(crate) struct Entry {
    file: PathBuf,
    /// The path of the documented item, empty for the crate.
    item: String,
    line: usize,
    /// What the test harness adds to the name for how it is tested: ` - compile fail`.
    how_shown: String,
    how: How,
    /// Whether rustdoc builds it in one program with the others, as it does from edition
    /// 2024: the harness runs those first, apart from the ones it builds alone.
    merged: bool,
}

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
enum How {
    /// The program runs, by the runner of this number, and is to panic or not.
    Runs {
        at: usize,
        should_panic: bool,
    },
    Ignored,
    /// What it was to do it does without running: built, or refused as `compile_fail` asks.
    Passed,
    Failed(String),
}

/// One example as the daemon writes it: what the module of it is, and how it goes when that
/// is known before it runs.
struct Written {
    entry: Entry,
    /// The module, when it is one: an ignored example is not built.
    module: Option<String>,
    marks: Marks,
}

/// Whether the crate is the examples of a library, which the daemon writes.
pub(crate) fn is_examples(db: &RootDatabase, krate: base_db::Crate) -> bool {
    let named = krate.extra_data(db).display_name.as_ref();
    named.is_some_and(|it| it.crate_name().as_str() == CRATE)
        && crate::crate_root_file(db, krate.into())
            .is_some_and(|it| it.parent().is_some_and(|it| it.ends_with(DIR)))
}

/// Whether the crate is a library as rustdoc reads it, with `cfg(doc)` and `cfg(doctest)`:
/// it is where the examples are found, and is never built.
pub(crate) fn is_documented(db: &RootDatabase, krate: base_db::Crate) -> bool {
    krate.cfg_options(db).check_atom(&cfg::CfgAtom::Flag(intern::sym::doctest))
}

/// Whether the function runs an example: the program of the examples starts at those alone.
pub(crate) fn is_runner(db: &RootDatabase, function: hir::Function) -> bool {
    let module = function.module(db);
    module.is_crate_root(db) && function.name(db).as_str().starts_with(RUNNER)
}

/// The numbers of the examples of the crate that run: the program of the examples is their
/// code alone, and what is around it.
pub(crate) fn running(db: &RootDatabase, examples: hir::Crate) -> rustc_hash::FxHashSet<String> {
    let declared = examples.root_module(db).declarations(db).into_iter();
    let functions = declared.filter_map(|it| match it {
        hir::ModuleDef::Function(it) => Some(it.name(db).as_str().to_owned()),
        _ => None,
    });
    functions.filter_map(|it| Some(it.strip_prefix(RUNNER)?.to_owned())).collect()
}

/// Whether the function of a crate of examples is built, with the numbers of the examples
/// that run: the ones of an example that does not are not.
pub(crate) fn is_built(
    db: &RootDatabase,
    function: hir::Function,
    running: &rustc_hash::FxHashSet<String>,
) -> bool {
    let path = function.module(db).path_to_root(db);
    let Some(example) = path.iter().rev().nth(1) else { return true };
    let name = example.name(db).map(|it| it.as_str().to_owned()).unwrap_or_default();
    name.strip_prefix("__doctest_").is_none_or(|it| running.contains(it))
}

/// Each crate of examples with the library as rustdoc reads it, which it depends on as built.
fn crates(db: &RootDatabase) -> Vec<(base_db::Crate, base_db::Crate)> {
    let all = base_db::all_crates(db);
    let documented: Vec<base_db::Crate> =
        all.iter().copied().filter(|&it| is_documented(db, it)).collect();
    let examples = all.iter().copied().filter(|&it| is_examples(db, it));
    examples
        .filter_map(|examples| {
            // The file of the examples is named after the package, and the library depends on
            // the build of it.
            let path = crate::crate_root_file(db, examples.into())?;
            let package = path.file_stem()?.to_str()?.to_owned();
            let deps = &examples.data(db).dependencies;
            let of = |lib: &&base_db::Crate| {
                let data = lib.data(db);
                let named = matches!(
                    &data.origin,
                    base_db::CrateOrigin::Local { name: Some(name), .. } if name.as_str() == package
                );
                named
                    && deps
                        .iter()
                        .any(|dep| dep.crate_id.data(db).root_file_id == data.root_file_id)
            };
            Some((examples, *documented.iter().find(of)?))
        })
        .collect()
}

/// The texts the crates of examples are to have that they do not have yet. The examples are
/// written first with all of them run; the ones rust-analyzer finds errors in then are not.
pub(crate) fn rewrites(db: &RootDatabase, target: &str) -> Vec<(vfs::FileId, String)> {
    let mut rewrites = Vec::new();
    for (examples, documented) in crates(db) {
        let file = examples.data(db).root_file_id;
        let written = hir::attach_db(db, || written(db, documented, target));
        let mut modules = String::from(REPORT);
        let mut ranges = Vec::new();
        for (at, it) in written.iter().enumerate() {
            let start = TextSize::of(&*modules);
            if let Some(module) = &it.module {
                // The `main` of an example is its own: what runs it from outside is in it.
                let run = match it.entry.how {
                    How::Runs { .. } => {
                        "pub(crate) fn __rustd_run() { super::__RustdReport::report(main()) }\n"
                    }
                    _ => "",
                };
                modules.push_str(&format!(
                    "#[allow(unused, non_snake_case, unused_extern_crates)]\npub mod __doctest_{at} {{\n{module}\n{run}}}\n"
                ));
            }
            ranges.push(TextRange::new(start, TextSize::of(&*modules)));
        }
        modules.push_str(RUNNERS);
        let now = db.file_text(file).text(db).to_string();
        let runs = |it: &&Written| matches!(it.entry.how, How::Runs { .. });
        let all: Vec<&Written> = written.iter().filter(runs).collect();
        if !now.starts_with(&modules) {
            rewrites.push((file, with_runners(&modules, &all)));
            continue;
        }
        let errors = hir::attach_db(db, || errors(db, file));
        let mut entries = Vec::new();
        for (it, range) in written.iter().zip(ranges) {
            let inside = errors.iter().filter(|(_, at)| range.contains_range(*at));
            let found: Vec<&(String, String)> = inside.map(|it| &it.0).collect();
            entries.push(Entry { how: verdict(it, &found), ..it.entry.clone() });
        }
        let running: Vec<&Written> = written
            .iter()
            .zip(&entries)
            .filter(|(_, entry)| matches!(entry.how, How::Runs { .. }))
            .map(|it| it.0)
            .collect();
        let text = with_runners(&modules, &running);
        lock(&WRITTEN).get_or_insert_default().insert(file, entries);
        if text != now {
            rewrites.push((file, text));
        }
    }
    rewrites
}

/// How an example goes, from the errors rust-analyzer found in it: their codes and what they
/// say.
fn verdict(it: &Written, errors: &[&(String, String)]) -> How {
    let said =
        || errors.iter().map(|(code, said)| format!("error[{code}]: {said}\n")).collect::<String>();
    match &it.entry.how {
        How::Passed if it.marks.compile_fail => {
            if errors.is_empty() {
                return How::Failed(
                    "Test compiled successfully, but it's marked `compile_fail`.\n\nrustd found \
                     no error in it: it has no borrow checker, and not all of rustc's other \
                     checks"
                        .to_owned(),
                );
            }
            let missing: Vec<&String> = it
                .marks
                .error_codes
                .iter()
                .filter(|code| !errors.iter().any(|(it, _)| it == *code))
                .collect();
            match missing.is_empty() {
                true => How::Passed,
                false => How::Failed(format!(
                    "{}Some expected error codes were not found: {missing:?}",
                    said()
                )),
            }
        }
        // An example that is to compile fails on the errors rust-analyzer is sure of alone.
        _ if !errors
            .iter()
            .any(|(code, _)| crate::SURE.contains(&&**code) || code == "syntax-error") =>
        {
            it.entry.how.clone()
        }
        How::Runs { .. } | How::Passed => {
            How::Failed(format!("{}Couldn't compile the test.", said()))
        }
        how => how.clone(),
    }
}

/// What ends an example whose `main` returns an error as a program's `main` ends.
const REPORT: &str = "trait __RustdReport { fn report(self); }
impl __RustdReport for () { fn report(self) {} }
impl<E: ::core::fmt::Debug> __RustdReport for ::core::result::Result<(), E> {
    fn report(self) {
        if let ::core::result::Result::Err(error) = self {
            ::std::eprintln!(\"Error: {error:?}\");
            ::std::process::exit(1)
        }
    }
}
";

fn with_runners(modules: &str, running: &[&Written]) -> String {
    let mut text = modules.to_owned();
    for it in running {
        let How::Runs { at, .. } = it.entry.how else { continue };
        text.push_str(&format!("pub fn {RUNNER}{at}() {{ __doctest_{at}::__rustd_run() }}\n"));
    }
    text
}

/// The errors rust-analyzer is sure of in the file, and where: those of an example that is to
/// fail to compile are any it finds.
fn errors(db: &RootDatabase, file: vfs::FileId) -> Vec<((String, String), TextRange)> {
    let config = ide_diagnostics::DiagnosticsConfig::test_sample();
    let resolve = ide_db::assists::AssistResolveStrategy::None;
    let syntax = ide_diagnostics::syntax_diagnostics(db, &config, file);
    let semantic = ide_diagnostics::semantic_diagnostics(db, &config, &resolve, file);
    syntax
        .into_iter()
        .chain(semantic)
        // A lint is an error only by the levels of the example's attributes, which rustc
        // and rust-analyzer do not read alike.
        .filter(|it| {
            let lint = matches!(
                it.code,
                ide_diagnostics::DiagnosticCode::RustcLint(_)
                    | ide_diagnostics::DiagnosticCode::Clippy(_)
                    | ide_diagnostics::DiagnosticCode::RaLint(..)
            );
            it.severity == ide_db::Severity::Error && !lint && it.range.file_id == file
        })
        .map(|it| ((it.code.as_str().to_owned(), it.message), it.range.range))
        .collect()
}

/// The examples of the library, in the order rustdoc names them.
fn written(db: &RootDatabase, documented: base_db::Crate, target: &str) -> Vec<Written> {
    let krate = hir::Crate::from(documented);
    let of_the_crate = OfTheCrate::read(db, krate);
    let name = documented.extra_data(db).display_name.as_ref();
    let name = name.map(|it| it.crate_name().to_string()).unwrap_or_default();
    let frame = Frame {
        crate_name: &name,
        attrs: &of_the_crate.attrs,
        no_crate_inject: of_the_crate.no_crate_inject,
    };
    let edition = krate.edition(db);
    let mut examples = extract::examples(db, krate);
    examples.sort_by(|a, b| (&a.file, a.line, &a.item).cmp(&(&b.file, b.line, &b.item)));
    let mut written = Vec::new();
    for (at, example) in examples.into_iter().enumerate() {
        let marks = example.marks;
        let how_shown = match &marks {
            it if it.compile_fail => " - compile fail",
            it if it.no_run => " - compile",
            it if it.should_panic && edition.at_least_2024() => " - should panic",
            _ => "",
        };
        let id: String = format!("{}_{}_0", example.file.display(), example.line)
            .chars()
            .map(|it| if it.is_ascii_alphanumeric() { it } else { '_' })
            .collect();
        let program = Program::of(&example.code, &frame, &id, edition);
        let ignored =
            marks.ignore || marks.ignored_on.iter().any(|it| target.contains(it.as_str()));
        let refused = refusal(&program.source, edition, &marks);
        // Rustdoc merges an ignored example too, when it parses.
        let parses = || ast::SourceFile::parse(&program.source, edition).errors().is_empty();
        let merged = edition.at_least_2024()
            && !marks.compile_fail
            && refused.is_none()
            && (!ignored || parses());
        let (how, module) = match () {
            _ if ignored => (How::Ignored, None),
            _ if marks.compile_fail => (How::Passed, Some(program.source)),
            _ => match refused.clone() {
                Some(why) => (How::Failed(why), None),
                None if marks.no_run => (How::Passed, Some(program.source)),
                None => (How::Runs { at, should_panic: marks.should_panic }, Some(program.source)),
            },
        };
        // A module that does not end where it should would take the ones after it.
        let (how, module) = match module {
            Some(module) if !whole(&module, edition) => match marks.compile_fail {
                true if marks.error_codes.is_empty() => (How::Passed, None),
                _ => (
                    How::Failed("Couldn't compile the test: its braces do not pair up.".to_owned()),
                    None,
                ),
            },
            module => (how, module),
        };
        let entry = Entry {
            file: example.file,
            item: example.item,
            line: example.line,
            how_shown: how_shown.to_owned(),
            how,
            merged,
        };
        written.push(Written { entry, module, marks });
    }
    written
}

/// Whether `module` is one module of its own when it is written as one.
fn whole(module: &str, edition: Edition) -> bool {
    let text = format!("mod m {{\n{module}\n}}\n");
    let file = ast::SourceFile::parse(&text, edition).tree();
    let items: Vec<ast::Item> = file.items().collect();
    matches!(&*items, [ast::Item::Module(it)] if it.syntax().text_range().end() + TextSize::of("\n") == TextSize::of(&*text))
}

/// Why an example is not one module among the others, when it is not: what only a crate of its
/// own can have.
fn refusal(source: &str, edition: Edition, marks: &Marks) -> Option<String> {
    let own = "which only a program of its own can have: rustd builds the examples of a library \
               as one crate";
    if marks.test_harness {
        return Some(
            "the example is marked `test_harness`, which rustd does not run yet".to_owned(),
        );
    }
    if let Some(asked) = marks.edition.as_deref().filter(|it| *it != edition.to_string()) {
        return Some(format!(
            "the example is of edition {asked}, the library of {edition}: rustd builds the \
             examples of a library in its edition"
        ));
    }
    let file = ast::SourceFile::parse(source, edition).tree();
    for attr in ast::HasAttrs::attrs(&file) {
        let path = attr.path().map(|it| it.syntax().text().to_string()).unwrap_or_default();
        if !matches!(&*path, "allow" | "warn" | "deny" | "forbid" | "expect" | "doc") {
            return Some(format!("the example has `#![{path}]`, {own}"));
        }
    }
    for node in file.syntax().descendants() {
        if let Some(krate) = ast::ExternCrate::cast(node.clone()) {
            let attrs = ast::HasAttrs::attrs(&krate);
            if attrs
                .into_iter()
                .any(|it| it.path().is_some_and(|it| it.syntax().text() == "macro_use"))
            {
                return Some(format!("the example has `#[macro_use] extern crate`, {own}"));
            }
        }
        let Some(segment) = ast::PathSegment::cast(node) else { continue };
        let in_visibility =
            segment.syntax().ancestors().any(|it| it.kind() == SyntaxKind::VISIBILITY);
        let in_module = segment.syntax().ancestors().any(|it| it.kind() == SyntaxKind::MODULE);
        if segment.crate_token().is_some() && !in_visibility {
            return Some(format!("the example names `crate`, {own}"));
        }
        if segment.super_token().is_some() && !in_visibility && !in_module {
            return Some(format!("the example names `super`, {own}"));
        }
    }
    None
}

/// The harness of the program of the examples of `examples`: `--list` says what each is and
/// how the ones that do not run went, and a number runs that example. `runners` are the
/// daemon's runners by their names, with their symbols.
pub(crate) fn harness(
    db: &RootDatabase,
    examples: base_db::Crate,
    runners: &[(String, Option<String>)],
) -> Result<String, String> {
    let file = examples.data(db).root_file_id;
    let entries = lock(&WRITTEN).as_ref().and_then(|it| it.get(&file).cloned());
    let entries = entries.ok_or("the examples of the library were not written")?;
    let mut arms = String::new();
    for entry in &entries {
        let How::Runs { at, .. } = entry.how else { continue };
        let name = format!("{RUNNER}{at}");
        let runner = runners.iter().find(|it| it.0 == name);
        let symbol = runner.and_then(|it| it.1.clone()).ok_or_else(|| {
            format!("the example at line {} has no runner of the daemon's", entry.line)
        })?;
        arms.push_str(&format!(
            "        \"{at}\" => {{\n            unsafe extern \"Rust\" {{\n                \
             #[link_name = {symbol:?}]\n                safe fn run();\n            }}\n            \
             run()\n        }}\n"
        ));
    }
    let listed = serde_json::to_string(&entries).map_err(|it| it.to_string())?;
    Ok(format!(
        "#![allow(warnings)]\nconst LISTED: &str = {listed:?};\nfn main() {{\n    \
         let asked = std::env::args().nth(1).unwrap_or_default();\n    match asked.as_str() {{\n        \
         \"--list\" => print!(\"{{LISTED}}\"),\n{arms}        _ => std::process::exit(2),\n    }}\n}}\n"
    ))
}

#[derive(Default)]
struct OfTheCrate {
    attrs: Vec<String>,
    no_crate_inject: bool,
}

impl OfTheCrate {
    fn read(db: &RootDatabase, krate: hir::Crate) -> OfTheCrate {
        use syntax::{AstNode, SyntaxKind, ast};
        let root = krate.root_file(db);
        let file = ast::SourceFile::parse(db.file_text(root).text(db), Edition::CURRENT).tree();
        let mut of_the_crate = OfTheCrate::default();
        let trees = file.syntax().descendants().filter(|it| it.kind() == SyntaxKind::TOKEN_TREE);
        // `test(..)` directly inside `doc(..)` of an attribute of the file itself.
        for tree in trees {
            let before = |node: &syntax::SyntaxNode| {
                let mut prev = node.prev_sibling_or_token();
                while prev.as_ref().is_some_and(|it| it.kind().is_trivia()) {
                    prev = prev.and_then(|it| it.prev_sibling_or_token());
                }
                prev.map(|it| it.to_string())
            };
            let outer = tree.parent().filter(|it| it.kind() == SyntaxKind::TOKEN_TREE);
            let in_doc = outer.as_ref().is_some_and(|it| before(it).as_deref() == Some("doc"));
            if before(&tree).as_deref() != Some("test") || !in_doc {
                continue;
            }
            for inner in tree.children().filter(|it| it.kind() == SyntaxKind::TOKEN_TREE) {
                if before(&inner).as_deref() == Some("attr") {
                    let text = inner.text().to_string();
                    of_the_crate.attrs.extend(split_attrs(&text[1..text.len() - 1]));
                }
            }
            let words = tree.children_with_tokens().filter_map(|it| it.into_token());
            of_the_crate.no_crate_inject |=
                words.into_iter().any(|it| it.text() == "no_crate_inject");
        }
        of_the_crate
    }
}

/// The attributes in a list separated by commas, which their own arguments have too.
fn split_attrs(list: &str) -> Vec<String> {
    let (mut attrs, mut depth, mut start) = (Vec::new(), 0, 0);
    for (at, byte) in list.bytes().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b',' if depth == 0 => {
                attrs.push(list[start..at].trim().to_owned());
                start = at + 1;
            }
            _ => {}
        }
    }
    attrs.push(list[start..].trim().to_owned());
    attrs.retain(|it| !it.is_empty());
    attrs
}

/// Which examples the arguments after `--` ask for.
#[derive(Default)]
struct Wanted {
    filters: Vec<String>,
    skipped: Vec<String>,
    exact: bool,
}

impl Wanted {
    /// `Err` is the argument that asks for something not done here.
    fn parse(args: &[String]) -> Result<Wanted, String> {
        let mut wanted = Wanted::default();
        let mut args = args.iter();
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--exact" => wanted.exact = true,
                "--skip" => wanted.skipped.extend(args.next().cloned()),
                // The examples run as many at a time as there are processors either way.
                "--test-threads" => _ = args.next(),
                _ if arg.starts_with("--test-threads=") => {}
                _ if arg.starts_with('-') => return Err(arg.clone()),
                _ => wanted.filters.push(arg.clone()),
            }
        }
        Ok(wanted)
    }

    fn has(&self, name: &str) -> bool {
        let is = |it: &String| if self.exact { name == it } else { name.contains(it.as_str()) };
        (self.filters.is_empty() || self.filters.iter().any(is)) && !self.skipped.iter().any(is)
    }
}

/// How an example ended.
enum Ended {
    Passed,
    Ignored,
    /// With what the harness shows of it.
    Failed(String),
}

/// What the harness shows of an example that ran and failed.
fn failure(ran: &std::process::Output) -> String {
    let (stdout, stderr) =
        (String::from_utf8_lossy(&ran.stdout), String::from_utf8_lossy(&ran.stderr));
    let mut shown = format!("Test executable failed ({}).", ran.status);
    if !stdout.is_empty() || !stderr.is_empty() {
        shown.push('\n');
        if !stdout.is_empty() {
            shown.push_str(&format!("\nstdout:\n{stdout}"));
        }
        if !stderr.is_empty() {
            shown.push_str(&format!("\nstderr:\n{stderr}"));
        }
    }
    shown
}

/// Runs the examples of the program at `binary`, each in a process of its own in `run_in`
/// with `env`, as `args` ask, and says how they went as rustdoc's test harness does. Their
/// files are named from `root`. The code to end with.
pub(crate) fn run(
    runner: &[String],
    binary: &Path,
    run_in: &Path,
    env: &[(String, String)],
    root: &Path,
    args: &[String],
) -> anyhow::Result<i32> {
    let start = Instant::now();
    let wanted = Wanted::parse(args).map_err(|it| {
        anyhow::anyhow!("the doc tests are run with `{it}`, which rustd does not read yet")
    })?;
    let listed = crate::cargo::running(runner, binary)
        .arg("--list")
        .output()
        .context("listing the examples")?;
    anyhow::ensure!(listed.status.success(), "the program of the examples did not list them");
    let entries: Vec<Entry> = serde_json::from_slice(&listed.stdout)?;
    let named = |it: &Entry| {
        let file = it.file.strip_prefix(root).unwrap_or(&it.file);
        let item = if it.item.is_empty() { String::new() } else { format!("{} ", it.item) };
        format!("{} - {item}(line {})", file.display(), it.line)
    };
    // Rustdoc builds every example alone when one of the ones it merges does not compile.
    let mut entries = entries;
    if entries.iter().any(|it| it.merged && matches!(it.how, How::Failed(_))) {
        for entry in &mut entries {
            entry.merged = false;
            if entry.how_shown == " - should panic" {
                entry.how_shown.clear();
            }
        }
    }
    let mut code = 0;
    let merged = entries.iter().any(|it| it.merged);
    for together in [true, false] {
        let (group, _): (Vec<Entry>, Vec<Entry>) =
            entries.iter().cloned().partition(|it| it.merged == together);
        // A library with no examples has its run of none said all the same.
        if group.is_empty() && (together || !entries.is_empty()) {
            continue;
        }
        let tests: Vec<(String, Entry)> = group.into_iter().map(|it| (named(&it), it)).collect();
        code = code.max(run_group(runner, binary, run_in, env, tests, &wanted)?);
    }
    if merged {
        let took = start.elapsed().as_secs_f64();
        writeln!(
            std::io::stdout(),
            "all doctests ran in {took:.2}s; merged doctests compilation took 0.00s"
        )?;
    }
    Ok(code)
}

/// Runs the examples `tests` asks for, by their names, and says how they went as one run of
/// the harness does.
fn run_group(
    runner: &[String],
    binary: &Path,
    run_in: &Path,
    env: &[(String, String)],
    mut tests: Vec<(String, Entry)>,
    wanted: &Wanted,
) -> anyhow::Result<i32> {
    let start = Instant::now();
    let all = tests.len();
    tests.retain(|(name, _)| wanted.has(name));
    tests.sort_by(|a, b| a.0.cmp(&b.0));
    let left_out = all - tests.len();
    let out = std::io::stdout();
    writeln!(&out, "\nrunning {} test{}", tests.len(), if tests.len() == 1 { "" } else { "s" })?;
    let next = Mutex::new(0);
    let ended: Mutex<Vec<(usize, Ended)>> = Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism().map_or(1, |it| it.get()).min(tests.len());
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let at = {
                        let mut next = lock(&next);
                        *next += 1;
                        *next - 1
                    };
                    let Some((name, entry)) = tests.get(at) else { break };
                    let result = match &entry.how {
                        How::Runs { at, should_panic } => {
                            let ran = crate::cargo::running(runner, binary)
                                .arg(at.to_string())
                                .current_dir(run_in)
                                .envs(env.iter().cloned())
                                .output();
                            match ran {
                                Err(error) => Ended::Failed(format!("Couldn't run the test: {error}")),
                                Ok(ran) => match (ran.status.success(), should_panic) {
                                    (true, false) | (false, true) => Ended::Passed,
                                    (true, true) => Ended::Failed(
                                        "Test executable succeeded, but it's marked `should_panic`."
                                            .to_owned(),
                                    ),
                                    (false, false) => Ended::Failed(failure(&ran)),
                                },
                            }
                        }
                        How::Ignored => Ended::Ignored,
                        How::Passed => Ended::Passed,
                        How::Failed(why) => Ended::Failed(why.clone()),
                    };
                    let word = match &result {
                        Ended::Passed => "ok",
                        Ended::Ignored => "ignored",
                        Ended::Failed(_) => "FAILED",
                    };
                    _ = writeln!(&out, "test {name}{} ... {word}", entry.how_shown);
                    lock(&ended).push((at, result));
                }
            });
        }
    });
    let mut ended = ended.into_inner().unwrap_or_else(|it| it.into_inner());
    ended.sort_by_key(|(at, _)| *at);
    let (mut passed, mut ignored, mut failed) = (0, 0, Vec::new());
    for (at, result) in ended {
        match result {
            Ended::Passed => passed += 1,
            Ended::Ignored => ignored += 1,
            Ended::Failed(shown) => {
                failed.push((format!("{}{}", tests[at].0, tests[at].1.how_shown), shown))
            }
        }
    }
    if !failed.is_empty() {
        writeln!(&out, "\nfailures:\n")?;
        for (name, shown) in &failed {
            writeln!(&out, "---- {name} stdout ----\n{shown}\n")?;
        }
        writeln!(&out, "\nfailures:")?;
        for (name, _) in &failed {
            writeln!(&out, "    {name}")?;
        }
    }
    writeln!(
        &out,
        "\ntest result: {}. {passed} passed; {} failed; {ignored} ignored; 0 measured; {left_out} filtered out; finished in {:.2}s\n",
        if failed.is_empty() { "ok" } else { "FAILED" },
        failed.len(),
        start.elapsed().as_secs_f64(),
    )?;
    Ok(if failed.is_empty() { 0 } else { FAILED })
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(|it| it.into_inner())
}
