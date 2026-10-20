//! rustd as cargo's `RUSTC_WORKSPACE_WRAPPER`: rustc builds the crates of the registry, and of
//! the workspace only what runs during the build. A library or program of the workspace is
//! built from a few lines that name the crates it depends on, so that rustc links the
//! program against them as it would have, and the code is rustd's to compile.
//!
//! What runs during the build is told from the rest by `--target`, which cargo passes for
//! the program's crates alone when it is given one itself.

use std::{ffi::OsString, path::Path, process::Command};

use anyhow::Context as _;

/// The flags of rustc that cargo passes with their value as the next argument.
pub(crate) const VALUED: &[&str] = &[
    "-C",
    "-L",
    "-Z",
    "-l",
    "-A",
    "-W",
    "-D",
    "-F",
    "--cfg",
    "--check-cfg",
    "--extern",
    "--out-dir",
    "--target",
    "--crate-name",
    "--crate-type",
    "--cap-lints",
    "--emit",
    "--edition",
    "--error-format",
    "--json",
    "--color",
    "--diagnostic-width",
    "--remap-path-prefix",
];

/// A `main` for cargo's link of a stand-in program to find. It is weak and of no code: the
/// link of what runs has rustd's.
const WEAK_MAIN: &str = r#"#[cfg(not(target_vendor = "apple"))]
core::arch::global_asm!(".weak main", "main:");
#[cfg(target_vendor = "apple")]
core::arch::global_asm!(".globl _main", ".weak_definition _main", "_main:");
"#;

/// Runs rustc as cargo asked, or on what stands in for a crate of the workspace.
pub(crate) fn command(mut args: impl Iterator<Item = OsString>) -> anyhow::Result<()> {
    let rustc = args.next().context("cargo names rustc first")?;
    let mut args: Vec<OsString> = args.collect();
    if let Some((source, text)) = stand_in(&args) {
        let out_dir = valued(&args, "--out-dir").context("cargo names where the output goes")?;
        let name = valued(&args, "--crate-name").unwrap_or_default();
        let extra = args
            .iter()
            .filter_map(|it| it.to_str()?.strip_prefix("extra-filename="))
            .next()
            .unwrap_or_default();
        let path = Path::new(out_dir).join(format!("{name}{extra}.rustd.rs"));
        std::fs::write(&path, text).with_context(|| format!("writing {}", path.display()))?;
        args[source] = path.into();
    }
    run(Command::new(rustc).args(args))
}

/// Becomes rustc.
#[cfg(unix)]
fn run(rustc: &mut Command) -> anyhow::Result<()> {
    use std::os::unix::process::CommandExt as _;
    Err(rustc.exec().into())
}

/// Windows has no process become another: rustc runs below this one, which ends as it did.
#[cfg(windows)]
fn run(rustc: &mut Command) -> anyhow::Result<()> {
    let status = rustc.status()?;
    std::process::exit(status.code().unwrap_or(1))
}

fn valued<'a>(args: &'a [OsString], flag: &str) -> Option<&'a str> {
    let at = args.iter().position(|it| it == flag)?;
    args.get(at + 1)?.to_str()
}

/// Where the source of the crate is among the arguments and what to build in its place, for
/// a library or a program of the workspace that is built for the target.
fn stand_in(args: &[OsString]) -> Option<(usize, String)> {
    let args: Vec<&str> = args.iter().map(|it| it.to_str()).collect::<Option<_>>()?;
    valued_in(&args, "--target")?;
    let program = is_program(&args)?;
    if args.contains(&"--test") || valued_in(&args, "--crate-name")?.starts_with("build_script_") {
        return None;
    }
    let source = (0..args.len())
        .find(|&at| args[at].ends_with(".rs") && !(at > 0 && VALUED.contains(&args[at - 1])))?;
    Some((source, text_of(&args, program)))
}

/// Whether rustc is asked for a program and nothing else, a test executable being one.
/// `None` when it is asked for neither that nor a Rust library alone: nothing stands in
/// for the crate then.
pub(crate) fn is_program<S: AsRef<str>>(args: &[S]) -> Option<bool> {
    let kinds = args.windows(2).filter(|it| it[0].as_ref() == "--crate-type");
    match *kinds.map(|it| it[1].as_ref()).collect::<Vec<_>>() {
        // Cargo names no type for a test target, which is a program to rustc.
        ["bin"] | [] => Some(true),
        ["lib" | "rlib"] => Some(false),
        _ => None,
    }
}

/// Whether rustc is asked for a test executable, whose `main` is the harness rustc writes.
fn is_test<S: AsRef<str>>(args: &[S]) -> bool {
    args.iter().any(|it| it.as_ref() == "--test")
}

/// The source that stands in for the crate rustc is given `args` for: it names the
/// libraries the crate is linked against and has no code. The `main` of a test executable
/// is the harness rustc writes, of no tests here: the daemon's harness takes its place.
pub(crate) fn text_of<S: AsRef<str>>(args: &[S], program: bool) -> String {
    let program = program && !is_test(args);
    let mut text = String::from("#![allow(warnings)]\n");
    if program {
        text.push_str("#![no_main]\n");
    }
    for pair in args.windows(2).filter(|it| it[0].as_ref() == "--extern") {
        let Some((name, path)) = pair[1].as_ref().split_once('=') else { continue };
        let name = name.rsplit_once(':').map_or(name, |it| it.1);
        // A proc macro is not linked into the program.
        if path.ends_with(".rlib") || path.ends_with(".rmeta") {
            text.push_str(&format!("extern crate {name};\n"));
        }
    }
    if program {
        text.push_str(WEAK_MAIN);
    }
    text
}

fn valued_in<'a>(args: &[&'a str], flag: &str) -> Option<&'a str> {
    let at = args.iter().position(|&it| it == flag)?;
    args.get(at + 1).copied()
}
