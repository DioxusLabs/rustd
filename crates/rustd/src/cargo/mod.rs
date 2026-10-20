//! `cargo rustd build|run|test|check`: cargo's commands, with the daemon building what
//! changed since cargo last built. `CARGO.md` at the root of the repository is the design.

pub(crate) mod daemon;
pub(crate) mod wrapper;

mod ancestor;
mod cli;
mod client;
mod clippy;
mod package;
pub(crate) mod plan;
pub(crate) mod run;
mod say;
pub(crate) mod script;
mod select;
mod state;

pub(crate) use state::running;
mod switch;
mod units;

use std::{collections::BTreeMap, path::Path, process::Command, time::Instant};

use anyhow::Context as _;

use cli::{Asked, Invocation, Subcommand};
use client::Start;
use daemon::{Checkout, Reply, Request};
use state::{Built, Counts, Staged, State};

/// `rustd cargo ...`: runs the command and ends with the status cargo would end with.
pub(crate) fn command(args: impl Iterator<Item = String>) -> anyhow::Result<()> {
    let args: Vec<String> = args.collect();
    let asked = Asked::parse(args);
    if !matches!(asked, Asked::Build(_) | Asked::Cargo(_)) {
        crate::end_with_reader();
    }
    let code = match asked {
        Asked::Build(asked) => match asked.unbuilt() {
            Some(why) => {
                say::error(&why);
                FAILED
            }
            None => build(&asked)?,
        },
        Asked::Cargo(args) => plain_cargo(args)?,
        Asked::Status => status()?,
        Asked::Stop => stop()?,
        Asked::Enable => switch::enable()?,
        Asked::Disable => switch::disable()?,
        Asked::Help => {
            println!("{HELP}");
            0
        }
    };
    std::process::exit(code)
}

const HELP: &str = "\
cargo rustd: builds with the rustd daemon, with cargo's flags

usage: cargo rustd <command> [cargo's flags]

  build, run, test   the workspace's crates by the daemon, what they depend on by rustc
  check              `cargo check`
  status             whether rustd is enabled, what the daemon has loaded, who built what
  stop               ends the daemon; the next build starts one
  enable, disable    plain `cargo build|run|test|check` through rustd, and back

Any other command is cargo's own. CARGO.md is the guide.";

/// Runs cargo with `args` and nothing of rustd's.
fn plain_cargo(args: Vec<String>) -> anyhow::Result<i32> {
    let status = Command::new(state::cargo_path()).args(args).status().context("running cargo")?;
    Ok(run::exit_code(status))
}

/// Builds what `asked` names and then runs what the subcommand runs. The crates of the
/// workspace are the daemon's to compile, in the first build and in every one after it;
/// cargo has rustc build what they depend on and what runs during the build. What the
/// daemon does not build fails the build: nothing of the workspace is handed to rustc.
fn build(asked: &Invocation) -> anyhow::Result<i32> {
    let started = Instant::now();
    let cwd = std::env::current_dir()?;
    let key = asked.key(&cwd);
    let (counts, state) = match State::read(&key) {
        Ok(state) => match by_daemon(state) {
            Ok(state) => (Counts::default(), Ok(state)),
            Err(Left::Failed(why)) => (Counts::default(), Err(NotBuilt::Daemons(why))),
            // What cargo acts on changed: cargo has rustc build what that changes of the
            // dependencies and of what runs during the build, and the daemon loads the rest.
            Err(Left::Again(state, why)) => {
                say::status(asked.flags.quiet, "Reloading", &why);
                (state.counts, Err(NotBuilt::Yet))
            }
        },
        Err(_) => (Counts::default(), Err(NotBuilt::Yet)),
    };
    let state = match state {
        Err(NotBuilt::Yet) => staged(asked, &cwd, &key, counts)?,
        state => state,
    };
    let state = match state {
        Ok(state) => state,
        Err(NotBuilt::Failed(code)) => return Ok(code),
        Err(NotBuilt::Daemons(why)) => {
            say::error(&why);
            return Ok(FAILED);
        }
        Err(NotBuilt::Yet) => anyhow::bail!("the build was not started"),
    };
    let took = started.elapsed().as_secs_f64();
    let finished = format!("`{}` profile [rustd] target(s) in {took:.2}s", state.profile);
    say::status(asked.flags.quiet, "Finished", &finished);
    state.write()?;
    after_build(asked, &state, &cwd)
}

/// The status of a build that failed, as cargo's of one rustc turned down.
const FAILED: i32 = 101;

/// Why a build has no programs.
enum NotBuilt {
    /// Cargo and the daemon have yet to build it.
    Yet,
    /// Cargo failed, with this status: rustc turned down something it builds.
    Failed(i32),
    /// The daemon does not build it, and why. Nothing else does.
    Daemons(String),
}

/// A build from what cargo has: cargo has rustc build what the workspace depends on and
/// what stands in for the crates of the workspace, and the daemon compiles those. Every
/// program is the daemon's: cargo linked only what stands in for it.
fn staged(
    asked: &Invocation,
    cwd: &Path,
    key: &str,
    counts: Counts,
) -> anyhow::Result<Result<State, NotBuilt>> {
    let crates = match Staged::of(asked)? {
        Ok(crates) => crates,
        Err(why) => return Ok(Err(NotBuilt::Daemons(why))),
    };
    State::give_back(key);
    let ahead = crates.ahead.as_ref().map(|ahead| {
        // Without an answer the daemon loads the workspace once cargo is done.
        let _ = client::ask(Request::Ahead(ahead.clone()), Start::IfMissing);
        ahead.config.id()
    });
    let state = match Built::staged(asked, &crates)? {
        Ok(built) => daemons(asked, cwd, key, built, counts)
            .unwrap_or_else(|why| Err(format!("{why:#}")))
            .map_err(NotBuilt::Daemons),
        Err(code) => Err(NotBuilt::Failed(code)),
    };
    if let (Err(_), Some(id)) = (&state, ahead) {
        let _ = client::ask(Request::Forget(id), Start::Never);
    }
    Ok(state)
}

/// The programs of a build whose workspace crates cargo built what stands in for, as the
/// daemon builds them. `Err` is why it did not build one.
fn daemons(
    asked: &Invocation,
    cwd: &Path,
    key: &str,
    built: Built,
    counts: Counts,
) -> anyhow::Result<Result<State, String>> {
    let state = State::after(asked, cwd, key, built, counts)?;
    Ok(first_by_daemon(state))
}

fn first_by_daemon(mut state: State) -> Result<State, String> {
    if let Some(why) = &state.refusal {
        return Err(why.clone());
    }
    if let Some((program, why)) = state.left_to_cargo().next() {
        return Err(format!("`{}`: {why}", program.name));
    }
    let answers = state.checkouts.iter().map(built).collect::<Result<Vec<_>, _>>()?;
    let cargos = state.settle(&answers)?;
    if let Some((_, why)) = cargos.first() {
        return Err(why.clone());
    }
    // What cargo linked stands in for the program, and is not what it is while its source
    // is unchanged: the daemon's is.
    state.keep_daemons().map_err(|why| format!("{why:#}"))?;
    state.counts.served += 1;
    Ok(state)
}

/// Why the daemon's programs are not the build.
enum Left {
    /// Something cargo acts on changed, and what: cargo is asked again, with the state so
    /// far.
    Again(Box<State>, String),
    /// The daemon did not build a program, and why.
    Failed(String),
}

/// Has the daemon bring the programs of `state` up to date and puts them where cargo has
/// them. Rustc sees none of it: the daemon builds what rust-analyzer passes, which has no
/// borrow checker and few of rustc's lints.
fn by_daemon(mut state: State) -> Result<State, Left> {
    let changed = state.refusal.clone().or_else(|| state.broken_guard());
    if let Some(reason) = changed.or_else(|| state.stale_cargos()) {
        return Err(Left::Again(Box::new(state), reason));
    }
    let answers =
        state.checkouts.iter().map(built).collect::<Result<Vec<_>, _>>().map_err(Left::Failed)?;
    let cargos = state.settle(&answers).map_err(Left::Failed)?;
    if let Some((_, why)) = cargos.first() {
        return Err(Left::Failed(why.clone()));
    }
    state.counts.served += 1;
    Ok(state)
}

/// Has the daemon build the programs of `checkout`, loading it first when it has not.
/// `Err` is why a program is not built.
pub(super) fn built(checkout: &Checkout) -> Result<Vec<Result<(), String>>, String> {
    if checkout.programs.is_empty() {
        return Ok(Vec::new());
    }
    let reply = client::ask(Request::Build(asking(checkout)), Start::IfMissing)
        .map_err(|it| format!("{it:#}"))?;
    let programs = match reply {
        Some(Reply::Synced { programs }) => programs,
        None => return Err(client::why_none()),
        Some(Reply::Cold { reason }) => return Err(reason),
        Some(other) => return Err(format!("the daemon answered {other:?}")),
    };
    std::iter::zip(&checkout.programs, programs)
        .map(|(program, built)| match built {
            Ok(_) => Ok(Ok(())),
            Err(why) => Err(format!("rustd did not build {}: {why}", program.binary.display())),
        })
        .collect()
}

/// `checkout` as a request names it: with the variables of this process, which `env!`
/// reads where cargo set none. The ones that make rustd the wrapper are cargo's alone.
fn asking(checkout: &Checkout) -> Checkout {
    let wraps = |name: &str| name == wrapper::DRIVEN || name == switch::VARIABLE;
    let mut env: BTreeMap<String, String> =
        std::env::vars().filter(|(name, _)| !wraps(name)).collect();
    env.extend(checkout.env.clone());
    Checkout { env, ..checkout.clone() }
}

/// What the subcommand does once the programs are built.
fn after_build(asked: &Invocation, state: &State, cwd: &Path) -> anyhow::Result<i32> {
    match asked.subcommand {
        Subcommand::Build => Ok(0),
        Subcommand::Clippy => clippy::report(asked, state),
        Subcommand::Run => match run::program(asked, state, cwd)? {
            Some(code) => Ok(code),
            None => {
                let bins = |it: &&state::Program| !it.test && it.kind == state::Kind::Bin;
                let names: Vec<&str> =
                    state.programs.iter().filter(bins).map(|it| it.name.as_str()).collect();
                say::error(&match names.as_slice() {
                    [] => "a bin target must be available for `cargo rustd run`".to_owned(),
                    names => format!(
                        "`cargo rustd run` could not determine which binary to run. Use the \
                         `--bin` option to specify a binary, or the `default-run` manifest \
                         key.\navailable binaries: {}",
                        names.join(", ")
                    ),
                });
                Ok(FAILED)
            }
        },
        Subcommand::Test if asked.flags.no_run => Ok(0),
        Subcommand::Test if asked.flags.doc => run::doc_tests(asked, state),
        Subcommand::Test => {
            let code = run::tests(asked, state, cwd)?;
            let stopped = code != 0 && !asked.flags.no_fail_fast;
            // Cargo 1.99 runs no doc tests when tests are picked by target or by name.
            let picked = asked.flags.selects_targets || !asked.positional.is_empty();
            if stopped || picked {
                return Ok(code);
            }
            Ok(code.max(run::doc_tests(asked, state)?))
        }
    }
}

/// `cargo rustd status`: the daemon, its workers, and how the builds of each checkout went.
fn status() -> anyhow::Result<i32> {
    use std::fmt::Write as _;
    let mut said = String::new();
    for line in switch::status(&std::env::current_dir()?) {
        let _ = writeln!(said, "{line}");
    }
    match client::ask(Request::Status, Start::Never)? {
        Some(Reply::Status(daemon)) => {
            let idle =
                daemon.idle_secs.map_or("never".to_owned(), |it| format!("after {it}s idle"));
            let _ = writeln!(
                said,
                "daemon: pid {}, version {}, exits {idle}",
                daemon.pid, daemon.version
            );
            for worker in daemon.workers {
                let _ = writeln!(
                    said,
                    "  worker: pid {}, {}, log {}",
                    worker.pid,
                    worker.project.display(),
                    worker.log.display()
                );
                for (root, warmth) in worker.checkouts {
                    let _ = writeln!(said, "    {}: {warmth}", root.display());
                }
            }
        }
        Some(Reply::Restart { version }) => {
            let _ = writeln!(
                said,
                "daemon: another build of rustd, version {version}; the next build replaces it"
            );
        }
        _ => said.push_str("daemon: not running\n"),
    }
    for state in State::all() {
        let to_cargo: u64 = state.counts.cargo.values().sum();
        let _ = writeln!(
            said,
            "{} ({}, {}): {} builds by the daemon, {to_cargo} by cargo",
            state.root.display(),
            state.profile,
            state.key,
            state.counts.served
        );
        for (reason, count) in &state.counts.cargo {
            let _ = writeln!(said, "  {count} x {reason}");
        }
        if let Some(refusal) = &state.refusal {
            let _ = writeln!(said, "  every build fails: {refusal}");
        }
    }
    // Whoever reads this may stop reading before its end.
    let _ = std::io::Write::write_all(&mut std::io::stdout(), said.as_bytes());
    Ok(0)
}

/// `cargo rustd stop`: has the daemon stop its workers and exit.
fn stop() -> anyhow::Result<i32> {
    match client::ask(Request::Stop, Start::Never)? {
        Some(_) => {
            client::gone(&daemon::socket_in(&daemon::home()?));
            println!("daemon: stopped");
        }
        None => println!("daemon: not running"),
    }
    Ok(0)
}
