use std::{
    io,
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::{ffi::OsString, os::unix::ffi::OsStringExt};

use rustc_hash::{FxHashMap, FxHashSet};
use vfs::FileId;

pub(crate) fn candidates(
    selected: &[(FileId, PathBuf)],
    edited: &FxHashSet<FileId>,
) -> Vec<FileId> {
    let mut roots = FxHashSet::default();
    let mut directories = FxHashSet::default();
    let mut dirty = FxHashSet::default();
    for (_, path) in selected {
        let Some(parent) = path.parent() else { continue };
        if !directories.insert(parent) {
            continue;
        }
        let root = toolchain::command("git", parent, &FxHashMap::default())
            .args(["rev-parse", "--show-toplevel"])
            .output();
        let Ok(root) = root else { continue };
        if !root.status.success() {
            continue;
        }
        let mut root = root.stdout;
        if root.last() == Some(&b'\n') {
            root.pop();
        }
        let Ok(root) = path_from_bytes(root) else { continue };
        if !roots.insert(root.clone()) {
            continue;
        }
        match git_dirty(&root) {
            Ok(paths) => dirty.extend(paths),
            Err(error) => eprintln!("predemote: git status in {}: {error}", root.display()),
        }
    }
    select(selected, edited, &dirty)
}

fn select(
    selected: &[(FileId, PathBuf)],
    edited: &FxHashSet<FileId>,
    dirty: &FxHashSet<PathBuf>,
) -> Vec<FileId> {
    selected
        .iter()
        .filter_map(|(id, path)| (edited.contains(id) || dirty.contains(path)).then_some(*id))
        .collect()
}

fn git_dirty(root: &Path) -> io::Result<FxHashSet<PathBuf>> {
    let status = toolchain::command("git", root, &FxHashMap::default())
        .args(["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules"])
        .output()?;
    if !status.status.success() {
        return Err(io::Error::other("git status failed"));
    }
    parse_status(root, &status.stdout)
}

fn parse_status(root: &Path, status: &[u8]) -> io::Result<FxHashSet<PathBuf>> {
    let mut paths = FxHashSet::default();
    let mut records = status.split_inclusive(|&byte| byte == 0);
    while let Some(record) = records.next() {
        let invalid = || io::Error::new(io::ErrorKind::InvalidData, "malformed git status");
        if record.len() < 5 || record[2] != b' ' || record.last() != Some(&0) {
            return Err(invalid());
        }
        paths.insert(root.join(path_from_bytes(record[3..record.len() - 1].to_vec())?));
        if record[..2].iter().any(|byte| matches!(byte, b'R' | b'C')) {
            let source = records.next().ok_or_else(invalid)?;
            if source.len() < 2 || source.last() != Some(&0) {
                return Err(invalid());
            }
            paths.insert(root.join(path_from_bytes(source[..source.len() - 1].to_vec())?));
        }
    }
    Ok(paths)
}

fn path_from_bytes(bytes: Vec<u8>) -> io::Result<PathBuf> {
    #[cfg(unix)]
    {
        Ok(OsString::from_vec(bytes).into())
    }
    #[cfg(not(unix))]
    {
        String::from_utf8(bytes)
            .map(PathBuf::from)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selected_candidates_keep_order_and_include_session_edits() {
        let selected = [(3, "a"), (1, "b"), (2, "c")]
            .map(|(id, path)| (FileId::from_raw(id), PathBuf::from(path)));
        let edited = [FileId::from_raw(2), FileId::from_raw(9)].into_iter().collect();
        let dirty = [PathBuf::from("a"), PathBuf::from("outside")].into_iter().collect();
        assert_eq!(select(&selected, &edited, &dirty), [FileId::from_raw(3), FileId::from_raw(2)]);
        assert!(select(&selected, &FxHashSet::default(), &FxHashSet::default()).is_empty());
        assert!(candidates(&[], &edited).is_empty());
    }

    #[test]
    fn status_includes_staged_unstaged_untracked_and_renamed_paths() {
        let root = Path::new("/repo");
        let paths =
            parse_status(root, b" M unstaged\0M  staged\0?? with space\0R  new\0old\0").unwrap();
        assert_eq!(
            paths,
            ["unstaged", "staged", "with space", "new", "old"]
                .map(|path| root.join(path))
                .into_iter()
                .collect()
        );
        assert!(parse_status(root, b"").unwrap().is_empty());
        assert!(parse_status(root, b" M missing nul").is_err());
        assert!(parse_status(root, b"R  new\0").is_err());
    }

    #[test]
    fn unavailable_checkout_keeps_session_edits_without_speculative_demotion() {
        let file = FileId::from_raw(1);
        let selected = [(file, PathBuf::from("/no-such-predemote-checkout/src.rs"))];
        assert!(git_dirty(Path::new("/no-such-predemote-checkout")).is_err());
        assert!(candidates(&selected, &FxHashSet::default()).is_empty());
        assert_eq!(candidates(&selected, &[file].into_iter().collect()), [file]);
    }
}
