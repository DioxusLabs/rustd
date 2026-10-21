//! Ruff exports a public struct explicitly beside a crate-visible glob of the same module.

use foreign::Issue;

pub fn run() -> u32 {
    Issue { value: 7 }.value()
}
