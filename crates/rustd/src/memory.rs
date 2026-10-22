//! Where the daemon's memory is.
//!
//! With `RUSTD_MEMORY` naming a directory, the daemon reports what the process holds after
//! each step of warming up, and once warm writes there what every ingredient of the database
//! holds. A build with the `heap-profile` feature allocates with jemalloc instead of
//! mimalloc: it can tell how much of the heap is live, and with `_RJEM_MALLOC_CONF=prof:true`
//! it writes a profile of the heap next to the ingredients, for `jeprof` to read.

use std::{
    fmt::Write as _,
    path::{Path, PathBuf},
};

use ide_db::{RootDatabase, base_db::salsa};

const GIB: u64 = 1024 * 1024 * 1024;

/// The directory `RUSTD_MEMORY` names, when it is set.
pub(crate) fn report_dir() -> Option<PathBuf> {
    std::env::var_os("RUSTD_MEMORY").map(PathBuf::from)
}

/// Megabytes of memory the process has resident.
pub(crate) fn resident() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find_map(|it| it.strip_prefix("VmRSS:"))?;
    Some(line.trim().trim_end_matches("kB").trim().parse::<u64>().ok()? / 1024)
}

/// Bytes of memory a worker has resident.
pub(crate) fn resident_bytes(pid: u32) -> Option<u64> {
    proc_bytes(&PathBuf::from(format!("/proc/{pid}/status")), "VmRSS:")
}

/// The limit before another root joins a worker, in bytes.
pub(crate) fn worker_budget() -> Option<u64> {
    std::env::var("RUSTD_WORKER_BUDGET")
        .ok()
        .and_then(|it| parse_budget(&it))
        .or_else(|| proc_bytes(Path::new("/proc/meminfo"), "MemTotal:").map(|it| it / 2))
}

fn proc_bytes(path: &Path, key: &str) -> Option<u64> {
    let contents = std::fs::read_to_string(path).ok()?;
    let line = contents.lines().find_map(|it| it.strip_prefix(key))?;
    let mut parts = line.split_whitespace();
    let value = parts.next()?.parse::<u64>().ok()?;
    (parts.next()? == "kB").then(|| value.checked_mul(1024)).flatten()
}

fn parse_budget(value: &str) -> Option<u64> {
    if let Some(gibibytes) = value.strip_suffix('G') {
        gibibytes.parse::<u64>().ok()?.checked_mul(GIB)
    } else {
        value.parse().ok()
    }
}

/// Bytes allocated and not freed, when the allocator counts them.
pub(crate) fn live() -> Option<u64> {
    #[cfg(feature = "heap-profile")]
    {
        tikv_jemalloc_ctl::epoch::advance().ok()?;
        tikv_jemalloc_ctl::stats::allocated::read().ok().map(|it| it as u64)
    }
    #[cfg(not(feature = "heap-profile"))]
    None
}

/// Reports what the process holds now that `step` is done.
pub(crate) fn checkpoint(step: &str) {
    if report_dir().is_none() {
        return;
    }
    let live = live().map(|it| format!(", {} MB live", it >> 20)).unwrap_or_default();
    eprintln!("memory after {step}: {} MB resident{live}", resident().unwrap_or(0));
}

/// Writes what the daemon holds now that `step` is done to the directory `RUSTD_MEMORY` names.
pub(crate) fn report(db: &mut RootDatabase, step: &str) -> anyhow::Result<()> {
    checkpoint(step);
    let Some(dir) = report_dir() else { return Ok(()) };
    std::fs::create_dir_all(&dir)?;
    write_heap_profile(&dir.join(format!("{step}.prof")))?;
    std::fs::write(dir.join(format!("{step}.tsv")), ingredients(db))?;
    Ok(())
}

/// A line for every struct and query of the database: how many there are and the bytes of
/// their fields, of the database's own records about them and, where the ingredient can
/// tell, of what the fields own on the heap.
fn ingredients(db: &mut RootDatabase) -> String {
    let db: &mut dyn salsa::Database = db;
    let usage = db.memory_usage();
    let structs = usage.structs.iter().map(|it| ("struct", it.debug_name(), it));
    let queries = usage.queries.iter().map(|(&name, it)| ("query", name, it));
    let mut rows: Vec<_> = structs.chain(queries).collect();
    rows.sort_by_key(|(_, _, it)| std::cmp::Reverse(it.size_of_fields() + it.size_of_metadata()));
    let mut table = String::from("kind\tcount\tfields\tmetadata\theap\tname\n");
    for (kind, name, it) in rows {
        let heap = it.heap_size_of_fields().map(|it| it.to_string()).unwrap_or_default();
        _ = writeln!(
            table,
            "{kind}\t{}\t{}\t{}\t{heap}\t{name}",
            it.count(),
            it.size_of_fields(),
            it.size_of_metadata(),
        );
    }
    table
}

#[cfg(feature = "heap-profile")]
fn write_heap_profile(path: &Path) -> anyhow::Result<()> {
    use std::os::unix::ffi::OsStrExt as _;

    // SAFETY: `opt.prof` is a `bool`.
    if !unsafe { tikv_jemalloc_ctl::raw::read::<bool>(b"opt.prof\0") }.unwrap_or(false) {
        return Ok(());
    }
    let path = std::ffi::CString::new(path.as_os_str().as_bytes())?;
    // SAFETY: `prof.dump` takes a C string, which `path` is for the length of the call.
    unsafe { tikv_jemalloc_ctl::raw::write(b"prof.dump\0", path.as_ptr()) }
        .map_err(|e| anyhow::anyhow!("writing the heap profile: {e}"))
}

#[cfg(not(feature = "heap-profile"))]
fn write_heap_profile(_: &Path) -> anyhow::Result<()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_worker_budget_bytes_and_gibibytes() {
        assert_eq!(parse_budget("123"), Some(123));
        assert_eq!(parse_budget("2G"), Some(2 * GIB));
        assert_eq!(parse_budget("0"), Some(0));
    }

    #[test]
    fn rejects_invalid_worker_budgets() {
        assert_eq!(parse_budget(""), None);
        assert_eq!(parse_budget("2GB"), None);
        assert_eq!(parse_budget("18446744073709551615G"), None);
    }
}
