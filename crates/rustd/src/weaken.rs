//! `rustd weaken FILE...`: copies of rustc's Mach-O objects and archives whose definitions
//! give way to rustd's.
//!
//! rustd's object is linked ahead of what rustc built of the same crates, and defines many of
//! the same names. An ELF linker is told to keep the first definition it meets. Apple's has no
//! such flag: two definitions of a name are an error unless one is weak, and of several weak
//! ones the first on the command line stays. So every definition of the copies is made weak,
//! and private to the program as well, which keeps the loader from looking for the name in
//! the libraries it loads. Nothing else of a file changes, and a file that is no Mach-O
//! object is copied as it is.

use std::{
    ops::Range,
    path::{Path, PathBuf},
};

use anyhow::Context as _;
use object::{
    LittleEndian as LE,
    macho::{LC_SYMTAB, MachHeader64, N_EXT, N_PEXT, N_SECT, N_STAB, N_TYPE, N_WEAK_DEF, Nlist64},
    pod,
    read::{
        archive::ArchiveFile,
        macho::{MachHeader as _, Nlist as _},
    },
};

/// The directory of the copies, in the one the files are in.
pub(crate) const DIR: &str = "rustd-weak";

/// Writes the copy of each file and prints where it is, in the order given.
pub(crate) fn command(args: impl Iterator<Item = String>) -> anyhow::Result<()> {
    for file in args {
        println!("{}", copy_of(Path::new(&file))?.display());
    }
    Ok(())
}

/// Writes the copy of `file`, unless the one there is of the file as it is, and says where
/// it is.
pub(crate) fn copy_of(file: &Path) -> anyhow::Result<PathBuf> {
    let (Some(dir), Some(name)) = (file.parent(), file.file_name()) else {
        anyhow::bail!("{} names no file", file.display());
    };
    let dir = dir.join(DIR);
    std::fs::create_dir_all(&dir)?;
    let copy = dir.join(name);
    if !up_to_date(&copy, file) {
        let mut data =
            std::fs::read(file).with_context(|| format!("reading {}", file.display()))?;
        weaken(&mut data);
        crate::replace(&copy, &data)?;
    }
    Ok(copy)
}

/// Whether the copy was written after the file it is of.
fn up_to_date(copy: &Path, file: &Path) -> bool {
    let written = |path: &Path| std::fs::metadata(path).and_then(|it| it.modified()).ok();
    matches!((written(copy), written(file)), (Some(copy), Some(file)) if copy > file)
}

/// Makes the definitions of an object, or of each object of an archive, weak.
fn weaken(data: &mut [u8]) {
    let members: Vec<Range<usize>> = match ArchiveFile::parse(&*data) {
        Ok(archive) => archive
            .members()
            .filter_map(|member| {
                let (start, len) = member.ok()?.file_range();
                Some(start as usize..(start + len) as usize)
            })
            .collect(),
        Err(_) => vec![0..data.len()],
    };
    for member in members {
        definitions(&mut data[member], |_| false);
    }
}

/// Makes the definitions of a Mach-O object weak, and private to what it is linked into
/// unless `visible` says its name, without Mach-O's leading `_`, is seen from outside it; an
/// object of another format stays as it is.
pub(crate) fn definitions(data: &mut [u8], visible: impl Fn(&str) -> bool) {
    let Some((symbols, strings)) = symbol_table(data) else { return };
    let Some(strings) = data.get(strings).map(<[u8]>::to_vec) else { return };
    let Some(data) = data.get_mut(symbols) else { return };
    let Ok(symbols) = pod::slice_from_all_bytes_mut::<Nlist64<LE>>(data) else { return };
    let name = |symbol: &Nlist64<LE>| {
        let name = strings.get(symbol.n_strx.get(LE) as usize..)?.split(|it| *it == 0).next()?;
        std::str::from_utf8(name).ok()?.strip_prefix('_')
    };
    for symbol in symbols {
        let defined = symbol.n_type & (N_STAB | N_TYPE) == N_SECT;
        if defined && symbol.n_type & N_EXT != 0 {
            if !name(symbol).is_some_and(&visible) {
                symbol.n_type |= N_PEXT;
            }
            symbol.n_desc.set(LE, symbol.n_desc(LE) | N_WEAK_DEF);
        }
    }
}

/// Where in a 64-bit Mach-O object its symbols are, and the names they have.
fn symbol_table(data: &[u8]) -> Option<(Range<usize>, Range<usize>)> {
    let header = MachHeader64::<LE>::parse(data, 0).ok()?;
    let mut commands = header.load_commands(LE, data, 0).ok()?;
    while let Ok(Some(command)) = commands.next() {
        if command.cmd() != LC_SYMTAB {
            continue;
        }
        let symtab = command.symtab().ok()??;
        let start = symtab.symoff.get(LE) as usize;
        let len = symtab.nsyms.get(LE) as usize * size_of::<Nlist64<LE>>();
        let strings = symtab.stroff.get(LE) as usize;
        return Some((start..start + len, strings..strings + symtab.strsize.get(LE) as usize));
    }
    None
}
