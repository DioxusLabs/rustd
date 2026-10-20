//! Running what was built, as cargo does: the program of `cargo run`, the test executables
//! of `cargo test`.

use std::{path::Path, process::ExitStatus};

use anyhow::Context as _;

use super::{
    cli::Invocation,
    say,
    select::Selective,
    state::{Kind, Program, State, as_staged, running},
};

/// The exit status of cargo when a test fails or a program can't be run.
const FAILED: i32 = 101;

/// Runs the program `asked` names, and ends as it ended. `None` when cargo has to say
/// which program that is: there are several, or none.
pub(crate) fn program(
    asked: &Invocation,
    state: &State,
    cwd: &Path,
) -> anyhow::Result<Option<i32>> {
    let runnable = |it: &&Program| !it.test && matches!(it.kind, Kind::Bin | Kind::Example);
    let mut programs: Vec<&Program> = state.programs.iter().filter(runnable).collect();
    match asked.flags.bin.as_ref().or(asked.flags.example.as_ref()) {
        Some(name) => programs.retain(|it| it.name == *name),
        // As cargo picks: the bin the package runs by default, among the bins it built.
        None => programs.retain(|it| it.default_run),
    }
    let &[program] = programs.as_slice() else { return Ok(None) };
    let shown = shown_path(&program.executable, cwd);
    let args = asked.program_args().map(|it| format!(" {it}")).collect::<String>();
    say::status(asked.flags.quiet, "Running", &format!("`{shown}{args}`"));
    let mut command = running(&state.runner, &program.executable);
    command.args(asked.program_args()).envs(program.env.iter().cloned());
    as_staged(&mut command)?;
    let status = command.status().with_context(|| format!("could not execute {shown}"))?;
    Ok(Some(exit_code(status)))
}

/// Runs the test executables one after another, each in the directory of its package, and
/// stops at the first that fails unless told not to. The result is cargo's exit status.
pub(crate) fn tests(asked: &Invocation, state: &State, cwd: &Path) -> anyhow::Result<i32> {
    let mut failed = Vec::new();
    for test in state.programs.iter().filter(|it| it.test) {
        let source = test.source.strip_prefix(&test.package_dir).unwrap_or(&test.source);
        let unit = if matches!(test.kind, Kind::Test | Kind::Bench) { "" } else { "unittests " };
        let shown = shown_path(&test.executable, cwd);
        say::status(asked.flags.quiet, "Running", &format!("{unit}{} ({shown})", source.display()));
        let selective = Selective::of(asked, state, test);
        let status = match selective.map(|it| it.run(asked)).transpose()?.flatten() {
            Some(status) => status,
            None => {
                let mut command = running(&state.runner, &test.executable);
                command.args(asked.program_args()).envs(test.env.iter().cloned());
                command.current_dir(&test.package_dir);
                as_staged(&mut command)?;
                command.status().with_context(|| format!("could not execute {shown}"))?
            }
        };
        if !status.success() {
            failed.push(rerun_flags(test));
            if !asked.flags.no_fail_fast {
                break;
            }
        }
    }
    match failed.as_slice() {
        [] => Ok(0),
        [one] => {
            say::error(&format!("test failed, to rerun pass `{one}`"));
            Ok(FAILED)
        }
        several => {
            say::error(&format!("{} targets failed:", several.len()));
            several.iter().for_each(|it| eprintln!("    `{it}`"));
            Ok(FAILED)
        }
    }
}

/// Runs the examples of the libraries whose doc tests cargo runs, a library after another,
/// and stops at the first that fails unless told not to. The result is cargo's exit status.
pub(crate) fn doc_tests(asked: &Invocation, state: &State) -> anyhow::Result<i32> {
    let mut failed = Vec::new();
    for why in &state.unrun_doc_tests {
        say::error(why);
        failed.push(None);
    }
    for library in state.programs.iter().filter(|it| it.kind == Kind::Doc) {
        if !failed.is_empty() && !asked.flags.no_fail_fast {
            break;
        }
        say::status(asked.flags.quiet, "Doc-tests", &library.name.replace('-', "_"));
        let args: Vec<String> = asked.program_args().cloned().collect();
        let code = crate::doctest::run(
            &state.runner,
            &library.executable,
            &library.package_dir,
            &library.env,
            &state.root,
            &args,
        )?;
        if code != 0 {
            failed.push(Some(rerun_flags(library)));
        }
    }
    match failed.as_slice() {
        [] => Ok(0),
        [Some(one)] => {
            say::error(&format!("doctest failed, to rerun pass `{one}`"));
            Ok(FAILED)
        }
        _ => Ok(FAILED),
    }
}

/// The flags that have cargo run this test target alone.
fn rerun_flags(test: &Program) -> String {
    let target = match test.kind {
        Kind::Lib => "--lib".to_owned(),
        Kind::Bin => format!("--bin {}", test.name),
        Kind::Example => format!("--example {}", test.name),
        Kind::Test => format!("--test {}", test.name),
        Kind::Bench => format!("--bench {}", test.name),
        Kind::Doc => "--doc".to_owned(),
    };
    format!("-p {} {target}", test.package)
}

/// The path as cargo shows it: from the directory the command runs in, when it is below.
fn shown_path(path: &Path, cwd: &Path) -> String {
    path.strip_prefix(cwd).unwrap_or(path).display().to_string()
}

/// What this command ends with after a process that ended with `status`: its code, or
/// the code a shell gives one a signal ended.
pub(crate) fn exit_code(status: ExitStatus) -> i32 {
    #[cfg(unix)]
    if let Some(signal) = std::os::unix::process::ExitStatusExt::signal(&status) {
        return 128 + signal;
    }
    status.code().unwrap_or(1)
}
