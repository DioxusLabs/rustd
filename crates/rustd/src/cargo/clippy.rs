//! `cargo rustd clippy`: once the daemon has built the programs, it is asked for clippy's
//! lints of their crates, which it keeps in its database and finds again only for the
//! bodies an edit changed. They are printed as clippy prints them.

use std::{collections::BTreeMap, path::Path};

use super::{
    asking,
    cli::Invocation,
    client::{self, Start},
    daemon::{Reply, Request},
    say,
    state::{Kind, State},
};
use crate::lint::{Finding, Level, Linted};

/// The exit status of cargo when a crate does not compile.
const FAILED: i32 = 101;

/// What clippy's lints `-D`, `-W` and `-A` after `--` set, in the order typed.
struct Levels(Vec<(String, Level)>);

impl Levels {
    fn of(trailing: &[String]) -> Levels {
        let mut set = Vec::new();
        let mut words = trailing.iter();
        while let Some(word) = words.next() {
            let level = |flag: &str| match flag {
                "-D" | "--deny" | "-F" | "--forbid" => Some(Level::Deny),
                "-W" | "--warn" => Some(Level::Warn),
                "-A" | "--allow" => Some(Level::Allow),
                _ => None,
            };
            let (level, name) = match level(word) {
                Some(level) => (level, words.next().cloned()),
                None => match word.get(..2).and_then(level) {
                    Some(level) => (level, Some(word[2..].to_owned())),
                    None => continue,
                },
            };
            if let Some(name) = name {
                set.push((name.replace('-', "_"), level));
            }
        }
        Levels(set)
    }

    /// The level of `finding`, and whether `-D warnings` made it so.
    fn of_finding(&self, finding: &Finding) -> (Level, bool) {
        let default = match finding.group.as_str() {
            "correctness" => Level::Deny,
            "style" | "complexity" | "suspicious" | "perf" => Level::Warn,
            _ => Level::Allow,
        };
        let names = [
            format!("clippy::{}", finding.lint),
            format!("clippy::{}", finding.group),
            "clippy::all".to_owned(),
        ];
        let typed = self.0.iter().rev().find(|(name, _)| names.contains(name)).map(|it| it.1);
        let level = finding.attributed.or(typed).unwrap_or(default);
        let warnings = self.0.iter().rev().find(|(name, _)| name == "warnings").map(|it| it.1);
        match (level, warnings) {
            (Level::Warn, Some(Level::Deny)) => (Level::Deny, true),
            (Level::Warn, Some(Level::Allow)) => (Level::Allow, false),
            _ => (level, false),
        }
    }
}

/// Prints the lints of the crates `state` built. The result is cargo's exit status.
pub(crate) fn report(asked: &Invocation, state: &State) -> anyhow::Result<i32> {
    let mut linted = Linted::default();
    for checkout in state.checkouts.iter().filter(|it| !it.programs.is_empty()) {
        let reply = client::ask(Request::Lint(asking(checkout)), Start::Never)?;
        let programs = match reply {
            Some(Reply::Synced { programs }) => programs,
            Some(Reply::Cold { reason }) => anyhow::bail!("the daemon did not lint: {reason}"),
            None => anyhow::bail!(client::why_none()),
            Some(other) => anyhow::bail!("the daemon answered {other:?}"),
        };
        for answer in programs {
            let answer = answer.map_err(|why| anyhow::anyhow!("the daemon did not lint: {why}"))?;
            let json = answer.strip_prefix("ok ").unwrap_or(&answer);
            let one: Linted = serde_json::from_str(json)?;
            linted.bodies += one.bodies;
            linted.anew += one.anew;
            linted.findings.extend(one.findings);
        }
    }
    if linted.bodies == 0 {
        say::error(
            "`cargo rustd clippy` lints the crates of the programs it builds, and this builds \
             none: a workspace of libraries alone is not linted yet",
        );
        return Ok(FAILED);
    }
    if std::env::var_os("RUSTD_STATS").is_some() {
        eprintln!("rustd: linted {} of {} bodies anew", linted.anew, linted.bodies);
    }
    linted.findings.sort();
    linted.findings.dedup();
    let levels = Levels::of(&asked.trailing);
    let mut targets: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut noted = Vec::new();
    for finding in &linted.findings {
        let (level, by_warnings) = levels.of_finding(finding);
        if level == Level::Allow {
            continue;
        }
        let first = !noted.contains(&finding.lint);
        if first {
            noted.push(finding.lint.clone());
        }
        let note = match () {
            _ if !first => None,
            _ if by_warnings => Some(format!(
                "`-D clippy::{}` implied by `-D warnings`",
                finding.lint.replace('_', "-")
            )),
            _ if finding.attributed.is_none() => {
                let word = if level == Level::Deny { "deny" } else { "warn" };
                Some(format!("`#[{word}(clippy::{})]` on by default", finding.lint))
            }
            _ => None,
        };
        eprint!("{}", shown(finding, level, &state.root, note.as_deref()));
        let counts = targets.entry(target(state, &finding.root)).or_default();
        match level {
            Level::Deny => counts.0 += 1,
            _ => counts.1 += 1,
        }
    }
    let mut failed = false;
    for (target, (errors, warnings)) in targets {
        let plural = |n: usize, word: &str| format!("{n} {word}{}", if n == 1 { "" } else { "s" });
        if errors == 0 {
            eprintln!("warning: {target} generated {}", plural(warnings, "warning"));
            continue;
        }
        failed = true;
        let emitted = match warnings {
            0 => String::new(),
            n => format!("; {} emitted", plural(n, "warning")),
        };
        say::error(&format!(
            "could not compile {target} due to {}{emitted}",
            plural(errors, "previous error")
        ));
    }
    Ok(if failed { FAILED } else { 0 })
}

/// The target a crate root is of, as cargo names it in its summary: `` `app` (bin "app") ``.
fn target(state: &State, root: &Path) -> String {
    let program = state.programs.iter().find(|it| it.source == root);
    let Some(program) = program else { return format!("`{}`", root.display()) };
    match program.kind {
        Kind::Lib => format!("`{}` (lib)", program.package),
        Kind::Bin => format!("`{}` (bin \"{}\")", program.package, program.name),
        Kind::Example => format!("`{}` (example \"{}\")", program.package, program.name),
        Kind::Test | Kind::Bench | Kind::Doc => {
            format!("`{}` (test \"{}\")", program.package, program.name)
        }
    }
}

/// A finding as rustc prints a diagnostic.
fn shown(finding: &Finding, level: Level, root: &Path, note: Option<&str>) -> String {
    let word = if level == Level::Deny { "error" } else { "warning" };
    let path = finding.path.strip_prefix(root).unwrap_or(&finding.path);
    let number = finding.line.to_string();
    let pad = " ".repeat(number.len());
    let carets = format!("{}{}", " ".repeat(finding.column - 1), "^".repeat(finding.width));
    let help = finding.help.as_deref().map(|it| format!(" help: {it}")).unwrap_or_default();
    let mut out = format!(
        "{word}: {}\n{pad}--> {}:{}:{}\n{pad} |\n{number} | {}\n{pad} | {carets}{help}\n{pad} |\n",
        finding.message,
        path.display(),
        finding.line,
        finding.column,
        finding.source,
    );
    out.push_str(&format!(
        "{pad} = help: for further information visit \
         https://rust-lang.github.io/rust-clippy/master/index.html#{}\n",
        finding.lint
    ));
    if let Some(note) = note {
        out.push_str(&format!("{pad} = note: {note}\n"));
    }
    out.push('\n');
    out
}
