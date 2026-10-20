//! The lines `cargo rustd` prints itself, in cargo's shape: a status word right-aligned in
//! twelve columns, on standard error.

use std::io::IsTerminal as _;

const GREEN: &str = "\x1b[1m\x1b[92m";
const RED: &str = "\x1b[1m\x1b[91m";
const RESET: &str = "\x1b[0m";

fn painted(color: &str, word: &str) -> String {
    match std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none() {
        true => format!("{color}{word}{RESET}"),
        false => word.to_owned(),
    }
}

/// `     Running target/debug/app`, unless the build is quiet.
pub(crate) fn status(quiet: bool, word: &str, rest: &str) {
    if !quiet {
        eprintln!(
            "{}{} {rest}",
            " ".repeat(12usize.saturating_sub(word.len())),
            painted(GREEN, word)
        );
    }
}

pub(crate) fn error(text: &str) {
    eprintln!("{}: {text}", painted(RED, "error"));
}
