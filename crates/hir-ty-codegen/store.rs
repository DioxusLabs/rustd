//! Compiled code kept on disk between runs of the daemon, by what it was compiled from.
//!
//! Nothing here knows about Rust: a key is a hash of what the value was made from, and the
//! value is whatever the caller serialized.
//!
//! # What is on disk
//!
//! The store is one directory:
//!
//! - `version` names the format of everything else in it. A daemon that finds an older
//!   format, or none in a directory that has files, empties the directory and starts over.
//!   One that finds a newer format leaves it alone and compiles without a store.
//! - `<sha256>.pack` is a sealed pack: the magic, then records. It is named by the hash of its
//!   bytes and never changes, so the same file can be on any machine or in a bucket. The
//!   hash is checked the first time a process reads the pack, and the checksum of a record
//!   every time its value is read. A pack that fails either is removed, and what was in it
//!   is compiled again.
//! - `<pid>-<nanos>.open` is the pack one daemon appends to, which it holds locked. An open
//!   pack nobody holds was left by a daemon that ended, and whoever finds it seals the
//!   records of it that are whole.
//! - `*.tmp` is a file on its way to another name, locked while it is written.
//! - `lock` is held by whoever empties the directory or collects garbage in it.
//!
//! A record is the key, the length of the value, a checksum of all three and the value. The
//! key on disk is not the caller's: it is hashed together with [`Identity`], so that a value
//! is only ever found by the build of rustd that wrote it, for the toolchain it wrote it for.
//!
//! # Why daemons that share a directory do not corrupt it
//!
//! Reading and adding take no lock. A sealed pack appears under its name by a rename, whole
//! and synced, and is never written again; an open pack is written by the one daemon that
//! holds its lock; and a file is taken out of the directory by unlinking it, which leaves it
//! whole for those that have it open. The `lock` file only keeps two collections, or a
//! collection and a change of format, from running at once.

use std::{
    borrow::Cow,
    fs::{File, OpenOptions},
    io::{self, Write},
    ops::Range,
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex, MutexGuard, OnceLock, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
    time::{Duration, SystemTime},
};

use cranelift_codegen::incremental_cache::CacheKvStore;
use rustc_hash::{FxHashMap, FxHashSet};
use sha2::{Digest, Sha256};

pub(super) const KEY: usize = 32;
/// The format of the directory, of a pack and of a record. A change to any of them is
/// another number here and another last byte of [`MAGIC`].
pub const FORMAT: u32 = 2;
const MAGIC: &[u8; 8] = b"rustdpk\x02";
const VERSION_FILE: &str = "version";
const LOCK_FILE: &str = "lock";
/// The key, the length of the value and the checksum of the record.
const HEADER: usize = KEY + 4 + 4;
/// An open pack smaller than this is left open: a pack per edit would be a pack per function.
const SEAL_AT: u64 = 4 << 20;
/// An open pack is sealed in the middle of a build at this many times the size it is sealed
/// at between builds, so that no pack is too much to send or fetch in one piece.
const ROLL_AFTER: u64 = 16;
/// Records wait in memory until there are this many bytes of them, or the build ends.
const WRITE_AT: usize = 64 << 10;
/// What the packs of a store may take when `RUSTD_CACHE_MAX` does not say.
const DEFAULT_LIMIT: u64 = 8 << 30;
/// More sealed packs than this that are smaller than [`SEAL_AT`] are made one: every daemon
/// that ends leaves one behind.
const SMALL_PACKS: usize = 16;
/// A temporary file nobody holds is only removed when it is older than this: its writer
/// creates it before it locks it.
const TEMPORARY_FOR: Duration = Duration::from_secs(60);
/// What a temporary file that holds the start of a pack being fetched ends in, before
/// `.tmp`: one that arrives as it is, and one that arrives compressed.
const FETCHED: [&str; 2] = [".fetch", ".zst"];
/// The start of a fetched pack that nobody holds is kept this long for a fetch to go on
/// from: it took a network to get.
const FETCHED_FOR: Duration = Duration::from_secs(24 * 60 * 60);

static TOOLCHAIN: OnceLock<String> = OnceLock::new();

/// Tells the store which toolchain built what the code of this process is linked against:
/// its commit, or anything else no two toolchains share. Without it nothing is kept.
pub fn compiles_against(toolchain: &str) {
    _ = TOOLCHAIN.set(toolchain.to_owned());
}

/// What the bytes of this process's executable come to.
fn program() -> Option<[u8; KEY]> {
    static PROGRAM: OnceLock<Option<[u8; KEY]>> = OnceLock::new();
    *PROGRAM.get_or_init(|| {
        let program = std::fs::read(std::env::current_exe().ok()?).ok()?;
        Some(Sha256::digest(program).into())
    })
}

/// Reads the executable on a thread of its own, for the store that is opened once the
/// workspace is loaded: it is tens of megabytes to hash.
pub fn identify_ahead() {
    if std::env::var_os("RUSTD_CACHE").is_some_and(|it| !is_off(&it)) {
        std::thread::spawn(program);
    }
}

/// What a value depends on that its key does not say: the format it is written in, the build
/// of rustd that made it and the toolchain it was made for.
#[derive(Clone, Copy)]
struct Identity([u8; KEY]);

impl Identity {
    fn new(build: &[u8], toolchain: &str) -> Identity {
        let mut hasher = Sha256::new();
        for field in [&FORMAT.to_le_bytes()[..], build, toolchain.as_bytes()] {
            hasher.update((field.len() as u64).to_le_bytes());
            hasher.update(field);
        }
        Identity(hasher.finalize().into())
    }

    /// Of this process: the bytes of its executable and the toolchain it was told of.
    fn current() -> io::Result<Identity> {
        let toolchain = TOOLCHAIN.get().ok_or_else(|| {
            io::Error::other("the toolchain the program was built with is not known")
        })?;
        let program = program().ok_or_else(|| io::Error::other("the program cannot be read"))?;
        Ok(Identity::new(&program, toolchain))
    }

    fn key(&self, key: &[u8; KEY]) -> [u8; KEY] {
        let mut hasher = Sha256::new();
        hasher.update(self.0);
        hasher.update(key);
        hasher.finalize().into()
    }
}

/// A size as it is written for people: bytes, or a number with `K`, `M` or `G` after it.
pub fn parse_size(text: &str) -> Option<u64> {
    let text = text.trim();
    let (digits, shift) = match text.as_bytes().last()?.to_ascii_uppercase() {
        b'K' => (&text[..text.len() - 1], 10),
        b'M' => (&text[..text.len() - 1], 20),
        b'G' => (&text[..text.len() - 1], 30),
        _ => (text, 0),
    };
    digits.parse::<u64>().ok()?.checked_mul(1 << shift)
}

/// The most the packs of a store may take, from `RUSTD_CACHE_MAX`: a size, or `off` for no
/// limit.
pub fn limit_from_env() -> Result<Option<u64>, String> {
    match std::env::var("RUSTD_CACHE_MAX") {
        Err(_) => Ok(Some(DEFAULT_LIMIT)),
        Ok(text) if text == "off" => Ok(None),
        Ok(text) => parse_size(&text)
            .map(Some)
            .ok_or_else(|| format!("RUSTD_CACHE_MAX=`{text}` is neither a size nor `off`")),
    }
}

/// The file name of a sealed pack with these bytes, or `None` if they are not a pack of the
/// format this build reads.
pub fn pack_name(bytes: &[u8]) -> Option<String> {
    bytes.starts_with(MAGIC).then(|| named(&Sha256::digest(bytes)))
}

/// The keys of the records of the pack `name`, in the order they were added, if its bytes are
/// what its name says and every record is as it was written. They are the keys as they are
/// on disk, which only the build of rustd that wrote them can make.
pub fn pack_keys(name: &str, bytes: &[u8]) -> Result<Vec<[u8; KEY]>, &'static str> {
    Ok(Pack::check(name, bytes)?.into_iter().map(|it| it.key).collect())
}

/// Asked for a key, as it is on disk, that no sealed pack of the store has: brings the pack
/// that has it into the store's directory, if it knows of one, and says whether it did.
pub type FetchMissing = Box<dyn Fn(&[u8; KEY]) -> bool + Send + Sync>;

static FETCH_MISSING: OnceLock<FetchMissing> = OnceLock::new();

/// Has the store of this process ask `fetch` for the keys it lacks, from now on. A process
/// has one store, and only the first call counts.
pub fn fetch_missing_with(fetch: FetchMissing) {
    _ = FETCH_MISSING.set(fetch);
}

/// Seals what the store of this process has open, however little it is, so that it can be
/// sent to other machines now. Between builds a small pack is otherwise left open.
pub fn seal_open() {
    if let Some(store) = Store::global() {
        store.settled();
        store.settle(1);
    }
}

/// Waits for the store of this process to have what the last build added. A process that
/// ends before it does leaves that to be compiled again.
pub fn settled() {
    if let Some(store) = Store::global() {
        store.settled();
    }
}

/// The format of the pack that starts with these bytes, if they start a pack of any.
pub fn pack_format(start: &[u8]) -> Option<u32> {
    let (format, name) = start.get(..MAGIC.len())?.split_last()?;
    (name == &MAGIC[..MAGIC.len() - 1]).then_some(u32::from(*format))
}

/// Whether `name` is what a sealed pack is called, and so safe to use as a file name.
pub fn is_pack(name: &str) -> bool {
    name.strip_suffix(".pack")
        .is_some_and(|hash| hash.len() == 64 && hash.bytes().all(|it| it.is_ascii_hexdigit()))
}

/// What a file in the directory of a store is, by its name. A file with any other name is
/// not the store's, and is never touched.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Pack,
    Open,
    /// On its way to the name it starts with, or left behind on the way.
    Temporary,
    Version,
}

impl Kind {
    fn of(name: &str) -> Option<Kind> {
        let numbers = |it: &str| {
            it.split_once('-').is_some_and(|(pid, at)| {
                !pid.is_empty()
                    && !at.is_empty()
                    && pid.bytes().chain(at.bytes()).all(|it| it.is_ascii_digit())
            })
        };
        if is_pack(name) {
            Some(Kind::Pack)
        } else if name == VERSION_FILE {
            Some(Kind::Version)
        } else if name.strip_suffix(".open").is_some_and(numbers) {
            Some(Kind::Open)
        } else {
            // The first format called these `.partial`.
            let whole = name.strip_suffix(".tmp").or_else(|| name.strip_suffix(".partial"))?;
            let (to, writer) = whole.rsplit_once('.')?;
            let numbered =
                !writer.is_empty() && writer.bytes().all(|it| it.is_ascii_digit() || it == b'-');
            // A pack on its way from a remote, as it is or compressed, is taken up by the
            // next process to fetch it; one compressed to be sent is made again.
            let fetched = matches!(writer, "fetch" | "zst" | "send") && is_pack(to);
            let of_the_store = numbered && (is_pack(to) || to == VERSION_FILE);
            (of_the_store || fetched).then_some(Kind::Temporary)
        }
    }
}

fn named(hash: &[u8]) -> String {
    use std::fmt::Write;
    let mut name = hash.iter().fold(String::with_capacity(hash.len() * 2 + 5), |mut out, byte| {
        _ = write!(out, "{byte:02x}");
        out
    });
    name.push_str(".pack");
    name
}

fn checksum(key: &[u8], value: &[u8]) -> u32 {
    let mut hasher = crc32fast::Hasher::new();
    hasher.update(key);
    hasher.update(&(value.len() as u32).to_le_bytes());
    hasher.update(value);
    hasher.finalize()
}

/// One record of a pack, by where its value is.
struct Record {
    key: [u8; KEY],
    value: Range<usize>,
    checksum: u32,
}

/// The records at the start of a pack that are as they were written, and how many bytes they
/// and the magic take. Whatever follows them was cut short or is not what was written.
fn records(pack: &[u8]) -> (Vec<Record>, usize) {
    let mut found = Vec::new();
    let mut at = MAGIC.len();
    if !pack.starts_with(MAGIC) {
        return (found, 0);
    }
    while let Some(header) = pack.get(at..at + HEADER) {
        let (key, rest) = header.split_at(KEY);
        let (len, sum) = rest.split_at(4);
        let len = u32::from_le_bytes(len.try_into().expect("four bytes")) as usize;
        let sum = u32::from_le_bytes(sum.try_into().expect("four bytes"));
        let start = at + HEADER;
        let Some(value) = start.checked_add(len).and_then(|end| pack.get(start..end)) else {
            break;
        };
        if checksum(key, value) != sum {
            break;
        }
        found.push(Record {
            key: key.try_into().expect("a key"),
            value: start..start + len,
            checksum: sum,
        });
        at = start + len;
    }
    (found, at)
}

/// The keys of the records a pack is laid out as, going by their lengths alone.
fn headed(pack: &[u8]) -> Vec<[u8; KEY]> {
    let mut keys = Vec::new();
    let mut at = MAGIC.len();
    if !pack.starts_with(MAGIC) {
        return keys;
    }
    while let Some(header) = pack.get(at..at + HEADER) {
        let (key, rest) = header.split_at(KEY);
        let len = u32::from_le_bytes(rest[..4].try_into().expect("four bytes")) as usize;
        at += HEADER + len;
        if at > pack.len() {
            break;
        }
        keys.push(key.try_into().expect("a key"));
    }
    keys
}

fn record(key: &[u8; KEY], value: &[u8], len: u32) -> Vec<u8> {
    let mut record = Vec::with_capacity(HEADER + value.len());
    record.extend_from_slice(key);
    record.extend_from_slice(&len.to_le_bytes());
    record.extend_from_slice(&checksum(key, value).to_le_bytes());
    record.extend_from_slice(value);
    record
}

/// Has the directory's entries on disk, so that a rename in it outlasts a loss of power.
fn sync_dir(dir: &Path) -> io::Result<()> {
    if cfg!(unix) {
        File::open(dir)?.sync_all()?;
    }
    Ok(())
}

fn nanos() -> u128 {
    SystemTime::UNIX_EPOCH.elapsed().map_or(0, |it| it.as_nanos())
}

/// Opens a sealed pack to read it and to say when it was last used. It can still be renamed
/// and removed by others while it is open, on Windows too: std shares a file for all three.
fn open_pack(path: &Path) -> io::Result<File> {
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt;
        const GENERIC_READ: u32 = 0x8000_0000;
        const FILE_WRITE_ATTRIBUTES: u32 = 0x0100;
        // The right to read does not bring the right to set a time there, and without it
        // a pack that is read from looks unused to a collection. Another user's pack may
        // not grant it: that one stays as old as it was.
        OpenOptions::new()
            .access_mode(GENERIC_READ | FILE_WRITE_ATTRIBUTES)
            .open(path)
            .or_else(|_| File::open(path))
    }
    #[cfg(not(windows))]
    {
        File::open(path)
    }
}

fn read_at(file: &File, buffer: &mut [u8], at: u64) -> io::Result<()> {
    #[cfg(unix)]
    {
        std::os::unix::fs::FileExt::read_exact_at(file, buffer, at)
    }
    #[cfg(windows)]
    {
        let mut done = 0;
        while done < buffer.len() {
            let at = at + done as u64;
            match std::os::windows::fs::FileExt::seek_read(file, &mut buffer[done..], at)? {
                0 => return Err(io::ErrorKind::UnexpectedEof.into()),
                read => done += read,
            }
        }
        Ok(())
    }
    // Where a file has no read at a place (wasm): nothing else reads this file here.
    #[cfg(not(any(unix, windows)))]
    {
        use std::io::{Read, Seek, SeekFrom};
        let mut file = file;
        file.seek(SeekFrom::Start(at))?;
        file.read_exact(buffer)
    }
}

/// The directory of a store, for what is done to it as a whole. Every one of these can run
/// while daemons read from the directory and add to it.
pub struct StoreDir {
    dir: PathBuf,
}

/// What [`StoreDir::stats`] counted. Sizes are in bytes.
#[derive(Debug, Default)]
pub struct Stats {
    /// The format the directory says it is of, if it says.
    pub format: Option<u32>,
    pub packs: usize,
    pub pack_bytes: u64,
    pub open: usize,
    pub open_bytes: u64,
    pub temporary: usize,
    pub temporary_bytes: u64,
    /// When the pack that has gone unused the longest was last used, and the one used last.
    pub used: Option<(SystemTime, SystemTime)>,
}

/// What [`StoreDir::collect`] did.
#[derive(Debug, Default)]
pub struct Collected {
    /// Another collection held the directory, and this one did nothing.
    pub busy: bool,
    pub evicted: usize,
    pub evicted_bytes: u64,
    /// Small packs that were made one.
    pub merged: usize,
    /// Open packs of daemons that ended, sealed or found empty.
    pub adopted: usize,
    /// Files on their way to another name that never got there.
    pub abandoned: usize,
    pub kept: usize,
    pub kept_bytes: u64,
}

/// Whether a file was refused for being another user's or open to others, which
/// [`StoreDir::open`] says in words of its own. The system refuses with the same kind and no
/// words: on Windows a pack that was evicted while a daemon still reads it can't be opened
/// until that daemon lets go of it, and is gone then, not wrong.
fn not_the_users(refused: &io::Error) -> bool {
    refused.kind() == io::ErrorKind::PermissionDenied && refused.get_ref().is_some()
}

/// What [`StoreDir::verify`] read.
#[derive(Debug, Default)]
pub struct Verified {
    pub format: Option<u32>,
    pub packs: usize,
    pub records: usize,
    pub bytes: u64,
    /// Sealed packs that are not what their names say, and why.
    pub corrupt: Vec<(String, String)>,
    /// Open packs, and the bytes at their ends that are not whole records.
    pub open: usize,
    pub torn_bytes: u64,
}

impl StoreDir {
    pub fn at(dir: &Path) -> StoreDir {
        StoreDir { dir: dir.to_owned() }
    }

    /// Makes the directory one this build reads and writes: creates it, and empties it when
    /// what is in it is of an older format. A directory of a newer format is an error, and
    /// is left as it is.
    pub fn claim(&self) -> io::Result<()> {
        private::create_dir(&self.dir)?;
        self.private()?;
        private::close(&self.dir)?;
        if self.format() == Some(FORMAT) {
            return Ok(());
        }
        let _held = self.lock()?;
        // Another daemon may have got here first.
        match self.format() {
            Some(FORMAT) => return Ok(()),
            Some(newer) if newer > FORMAT => {
                return Err(io::Error::other(format!(
                    "the store is of format {newer}, and this rustd reads format {FORMAT}"
                )));
            }
            _ => {}
        }
        let mut discarded = 0;
        for name in self.names()?.iter().filter(|it| Kind::of(it).is_some()) {
            std::fs::remove_file(self.dir.join(name))?;
            discarded += 1;
        }
        if discarded != 0 {
            eprintln!("store: {discarded} files of another format discarded");
        }
        self.write_whole(VERSION_FILE, format!("rustd store {FORMAT}\n").as_bytes())
    }

    /// Refuses a directory that is another user's or that others can write to: whoever
    /// can write a pack into it decides what the programs built from it run.
    fn private(&self) -> io::Result<()> {
        let refused = |why: &str| {
            let said = format!("the store {} {why}", self.dir.display());
            Err(io::Error::new(io::ErrorKind::PermissionDenied, said))
        };
        // A link to a directory is taken for the directory, which is what is checked.
        let dir = private::open_dir(&self.dir)?;
        if !dir.metadata()?.is_dir() {
            return refused("is not a directory");
        }
        match private::others_write(&dir) {
            Some(why) => refused(&format!("{why} ({} if it is yours)", private::MENDED_BY)),
            None => Ok(()),
        }
    }

    /// Opens a file of the store to read, and to write when `write` is set. One that is
    /// another user's or that others can write to is not the store's.
    fn open(&self, name: &str, write: bool) -> io::Result<File> {
        let file = OpenOptions::new().read(true).write(write).open(self.dir.join(name))?;
        match private::others_write(&file) {
            Some(why) => Err(io::Error::new(io::ErrorKind::PermissionDenied, why)),
            None => Ok(file),
        }
    }

    /// The bytes of a file of the store, as [`Self::open`] takes it for one.
    fn read(&self, name: &str) -> io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        io::Read::read_to_end(&mut self.open(name, false)?, &mut bytes)?;
        Ok(bytes)
    }

    /// The format the directory says it is of. One with packs and nothing that says is of
    /// the first format, which had no such file. `None` is a directory with nothing of a
    /// store in it.
    fn format(&self) -> Option<u32> {
        if let Ok(text) = self.read(VERSION_FILE) {
            // Text that is no version is of no format this build knows how to read.
            let text = String::from_utf8_lossy(&text);
            let format = text.trim().strip_prefix("rustd store ").and_then(|it| it.parse().ok());
            return Some(format.unwrap_or(0));
        }
        // A daemon that ended while it was saying which format the store is of left only
        // the start of that file, which the first format never had.
        let said = |name: &str| name.starts_with(VERSION_FILE);
        self.names().ok()?.iter().any(|it| Kind::of(it).is_some() && !said(it)).then_some(1)
    }

    /// Waits for the directory to be this process's to empty or collect.
    fn lock(&self) -> io::Result<File> {
        let file = self.lock_file()?;
        file.lock()?;
        Ok(file)
    }

    fn lock_file(&self) -> io::Result<File> {
        let path = self.dir.join(LOCK_FILE);
        let mut options = OpenOptions::new();
        private::file(options.create(true).truncate(false).write(true)).open(&path)
    }

    /// Writes a file that readers see all of or not at all, and that is whole after a loss
    /// of power once this returns.
    pub fn write_whole(&self, name: &str, bytes: &[u8]) -> io::Result<()> {
        write_whole(&self.dir.join(name), bytes, true)
    }

    /// The names of the files in the directory. One that is not there has none, and one
    /// that others can write to is refused.
    fn names(&self) -> io::Result<Vec<String>> {
        let entries = match std::fs::read_dir(&self.dir) {
            Ok(entries) => entries,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e),
        };
        self.private()?;
        let mut names = Vec::new();
        for entry in entries {
            if let Ok(name) = entry?.file_name().into_string() {
                names.push(name);
            }
        }
        Ok(names)
    }

    /// The names of the sealed packs.
    pub fn packs(&self) -> io::Result<Vec<String>> {
        Ok(self.names()?.into_iter().filter(|it| is_pack(it)).collect())
    }

    /// The keys, as they are on disk, that the sealed packs say they hold. A collection
    /// makes one pack of many, so what a store holds is told by its keys and not by the
    /// names of its packs.
    ///
    /// Only the headers of the records are read, not what they hold, so this is no check: a
    /// damaged pack may be said to hold a key that a build will not get from it.
    pub fn keys(&self) -> io::Result<FxHashSet<[u8; KEY]>> {
        let mut keys = FxHashSet::default();
        for name in self.packs()? {
            // Evicted since it was listed.
            let Ok(file) = File::open(self.dir.join(name)) else { continue };
            // SAFETY: a sealed pack is never written again; one that is removed stays
            // mapped.
            let Ok(pack) = (unsafe { memmap2::Mmap::map(&file) }) else { continue };
            keys.extend(headed(&pack));
        }
        Ok(keys)
    }

    /// Seals the open packs that daemons that are gone left behind, as far as their records
    /// are whole. Returns how many there were.
    pub fn adopt(&self) -> usize {
        let Ok(names) = self.names() else { return 0 };
        let mut adopted = 0;
        for name in names.iter().filter(|it| Kind::of(it) == Some(Kind::Open)) {
            let path = self.dir.join(name);
            let Ok(file) = self.open(name, true) else { continue };
            // Its daemon holds it for as long as it runs.
            if file.try_lock().is_err() {
                continue;
            }
            adopted += 1;
            if self.seal_left(&path, &file).is_err() {
                _ = std::fs::remove_file(&path);
            }
        }
        if adopted != 0 {
            _ = sync_dir(&self.dir);
        }
        adopted
    }

    /// Gives an open pack that is held here the name of its whole records, or removes it
    /// when it has none.
    fn seal_left(&self, path: &Path, mut file: &File) -> io::Result<()> {
        let mut pack = Vec::new();
        io::Read::read_to_end(&mut file, &mut pack)?;
        let (records, whole) = records(&pack);
        if records.is_empty() {
            return std::fs::remove_file(path);
        }
        if whole != pack.len() {
            file.set_len(whole as u64)?;
        }
        file.sync_all()?;
        std::fs::rename(path, self.dir.join(named(&Sha256::digest(&pack[..whole]))))
    }

    /// Counts what is in the directory without reading any of it.
    pub fn stats(&self) -> io::Result<Stats> {
        let mut stats = Stats { format: self.format(), ..Stats::default() };
        for name in self.names()? {
            // Gone since it was listed.
            let Ok(meta) = std::fs::metadata(self.dir.join(&name)) else { continue };
            let (count, bytes) = match Kind::of(&name) {
                Some(Kind::Pack) => {
                    if let Ok(at) = meta.modified() {
                        let (first, last) = stats.used.unwrap_or((at, at));
                        stats.used = Some((first.min(at), last.max(at)));
                    }
                    (&mut stats.packs, &mut stats.pack_bytes)
                }
                Some(Kind::Open) => (&mut stats.open, &mut stats.open_bytes),
                Some(Kind::Temporary) => (&mut stats.temporary, &mut stats.temporary_bytes),
                Some(Kind::Version) | None => continue,
            };
            *count += 1;
            *bytes += meta.len();
        }
        Ok(stats)
    }

    /// Reads every pack and checks it against its name and its records against their
    /// checksums. Changes nothing.
    pub fn verify(&self) -> io::Result<Verified> {
        let mut verified = Verified { format: self.format(), ..Verified::default() };
        for name in self.names()? {
            if Kind::of(&name) == Some(Kind::Open) {
                let Ok(pack) = self.read(&name) else { continue };
                verified.open += 1;
                verified.torn_bytes += (pack.len() - records(&pack).1) as u64;
                continue;
            }
            if !is_pack(&name) {
                continue;
            }
            let pack = match self.read(&name) {
                Ok(pack) => pack,
                Err(e) if not_the_users(&e) => {
                    verified.corrupt.push((name, e.to_string()));
                    continue;
                }
                // Evicted since it was listed.
                Err(_) => continue,
            };
            match Pack::check(&name, &pack) {
                Ok(records) => {
                    verified.packs += 1;
                    verified.records += records.len();
                    verified.bytes += pack.len() as u64;
                }
                Err(why) => verified.corrupt.push((name, why.to_owned())),
            }
        }
        Ok(verified)
    }

    /// Collects garbage: seals what ended daemons left open, removes what never got its
    /// name, makes one pack of the many small ones, and removes the packs that have gone
    /// unused the longest until the rest take no more than `limit` bytes.
    ///
    /// A daemon that has a removed pack open goes on reading it; one that starts later
    /// compiles what was in it.
    pub fn collect(&self, limit: Option<u64>) -> io::Result<Collected> {
        let lock = self.lock_file()?;
        if lock.try_lock().is_err() {
            return Ok(Collected { busy: true, ..Collected::default() });
        }
        let mut collected = Collected { adopted: self.adopt(), ..Collected::default() };
        collected.abandoned = self.remove_abandoned()?;
        collected.merged = self.merge_small()?;
        let mut packs = self.by_last_use()?;
        let mut total: u64 = packs.iter().map(|it| it.len).sum();
        let evicted = match limit {
            Some(limit) => {
                let mut keep_from = 0;
                while total > limit && keep_from < packs.len() {
                    total -= packs[keep_from].len;
                    keep_from += 1;
                }
                packs.drain(..keep_from).collect()
            }
            None => Vec::new(),
        };
        for pack in &evicted {
            if std::fs::remove_file(self.dir.join(&pack.name)).is_ok() {
                collected.evicted += 1;
                collected.evicted_bytes += pack.len;
            }
        }
        if collected.evicted + collected.merged + collected.abandoned != 0 {
            sync_dir(&self.dir)?;
        }
        (collected.kept, collected.kept_bytes) = (packs.len(), total);
        Ok(collected)
    }

    /// The sealed packs, the one that has gone unused the longest first.
    fn by_last_use(&self) -> io::Result<Vec<Listed>> {
        let mut packs = Vec::new();
        for name in self.packs()? {
            let Ok(meta) = std::fs::metadata(self.dir.join(&name)) else { continue };
            let used = meta.modified().unwrap_or(SystemTime::UNIX_EPOCH);
            packs.push(Listed { name, len: meta.len(), used });
        }
        packs.sort_unstable_by(|a, b| (a.used, &a.name).cmp(&(b.used, &b.name)));
        Ok(packs)
    }

    fn remove_abandoned(&self) -> io::Result<usize> {
        let mut abandoned = 0;
        for name in self.names()?.iter().filter(|it| Kind::of(it) == Some(Kind::Temporary)) {
            let path = self.dir.join(name);
            let Ok(file) = File::open(&path) else { continue };
            let fetched = name
                .strip_suffix(".tmp")
                .is_some_and(|it| FETCHED.iter().any(|end| it.ends_with(end)));
            let kept = if fetched { FETCHED_FOR } else { TEMPORARY_FOR };
            let old = file
                .metadata()
                .and_then(|it| it.modified())
                .is_ok_and(|at| at.elapsed().is_ok_and(|it| it > kept));
            if old && file.try_lock().is_ok() && std::fs::remove_file(&path).is_ok() {
                abandoned += 1;
            }
        }
        Ok(abandoned)
    }

    /// Makes one pack of the sealed packs smaller than [`SEAL_AT`] when there are many, and
    /// returns how many it took in. The new pack is there before the old ones go, so a key
    /// is in the directory throughout.
    fn merge_small(&self) -> io::Result<usize> {
        let small: Vec<Listed> =
            self.by_last_use()?.into_iter().filter(|it| it.len < SEAL_AT).collect();
        if small.len() <= SMALL_PACKS {
            return Ok(0);
        }
        let mut merged = MAGIC.to_vec();
        let mut keys = FxHashSet::default();
        let mut taken = Vec::new();
        for listed in &small {
            let Ok(pack) = self.read(&listed.name) else { continue };
            // One that is not what its name says is left for whoever reads it to remove.
            let Ok(records) = Pack::check(&listed.name, &pack) else { continue };
            if merged.len() + pack.len() > (SEAL_AT * ROLL_AFTER) as usize {
                break;
            }
            for record in records {
                if keys.insert(record.key) {
                    merged.extend_from_slice(&pack[record.value.start - HEADER..record.value.end]);
                }
            }
            taken.push(listed);
        }
        let (Some(last), true) = (taken.last(), taken.len() > 1) else { return Ok(0) };
        let name = named(&Sha256::digest(&merged));
        self.write_whole(&name, &merged)?;
        // As lately used as the last of what it was made of.
        if let Ok(file) = File::options().write(true).open(self.dir.join(&name)) {
            _ = file.set_modified(last.used);
        }
        for listed in &taken {
            if listed.name != name {
                _ = std::fs::remove_file(self.dir.join(&listed.name));
            }
        }
        Ok(taken.len())
    }
}

/// A sealed pack as a listing of the directory shows it.
struct Listed {
    name: String,
    len: u64,
    used: SystemTime,
}

fn write_whole(to: &Path, bytes: &[u8], private: bool) -> io::Result<()> {
    let dir = to.parent().ok_or(io::ErrorKind::InvalidInput)?;
    let name = to.file_name().ok_or(io::ErrorKind::InvalidInput)?.to_string_lossy();
    let partial = dir.join(format!("{name}.{}-{}.tmp", std::process::id(), nanos()));
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    if private {
        private::file(&mut options);
    }
    let mut file = options.open(&partial)?;
    let written = file
        .lock()
        .and_then(|()| file.write_all(bytes))
        .and_then(|()| name_file_whole(&file, &partial, to));
    if written.is_err() {
        _ = std::fs::remove_file(&partial);
    }
    written
}

/// Gives the file at `from`, which the caller wrote and holds, the name `to`: readers see
/// all of it or none, and it is whole after a loss of power once this returns. This is how
/// a file that arrives in pieces, as one fetched from a remote does, ends the way
/// [`write_file_whole`] writes one. In a store `from` is `<to>.<anything>.tmp`, so that what
/// a stopped process leaves is known for what it is.
pub fn name_file_whole(file: &File, from: &Path, to: &Path) -> io::Result<()> {
    file.sync_all()?;
    std::fs::rename(from, to)?;
    sync_dir(to.parent().ok_or(io::ErrorKind::InvalidInput)?)
}

/// Writes a file outside a store the way [`StoreDir::write_whole`] writes one inside.
pub fn write_file_whole(to: &Path, bytes: &[u8]) -> io::Result<()> {
    write_whole(to, bytes, false)
}

pub(super) struct Store {
    dir: StoreDir,
    identity: Identity,
    tuning: Tuning,
    sealed: RwLock<Sealed>,
    writer: Mutex<Writer>,
    hits: AtomicUsize,
    misses: AtomicUsize,
    /// Sealed packs that were not what their names say, and values that were not what
    /// their checksums say, since the last report.
    corrupt: AtomicUsize,
    /// The thread that settles what the last build added, until someone waits for it.
    settling: Mutex<Option<std::thread::JoinHandle<()>>>,
}

#[derive(Clone, Copy)]
struct Tuning {
    /// The size an open pack is sealed at between builds.
    seal_at: u64,
    limit: Option<u64>,
}

impl Tuning {
    /// `RUSTD_CACHE_MAX` and `RUSTD_CACHE_SEAL_AT`, a size each.
    fn from_env() -> io::Result<Tuning> {
        let limit = limit_from_env().map_err(io::Error::other)?;
        let seal_at = match std::env::var("RUSTD_CACHE_SEAL_AT") {
            Err(_) => SEAL_AT,
            Ok(text) => parse_size(&text).filter(|&it| it != 0).ok_or_else(|| {
                io::Error::other(format!("RUSTD_CACHE_SEAL_AT=`{text}` is not a size"))
            })?,
        };
        Ok(Tuning { seal_at, limit })
    }
}

/// The sealed packs this process has read.
#[derive(Default)]
struct Sealed {
    packs: FxHashMap<String, Arc<Pack>>,
    index: FxHashMap<[u8; KEY], Place>,
}

/// A sealed pack that was what its name says when it was first read.
struct Pack {
    name: String,
    file: File,
    /// Whether a value of it was read since its time of last use was last set.
    used: AtomicBool,
    /// Whether it was found to have changed since it was first read.
    changed: AtomicBool,
}

/// Where a value is.
#[derive(Clone)]
struct Place {
    pack: Arc<Pack>,
    at: u64,
    len: u32,
    checksum: u32,
}

impl Pack {
    /// The records of a pack whose bytes are what its name says, or what is wrong with it.
    fn check(name: &str, bytes: &[u8]) -> Result<Vec<Record>, &'static str> {
        if !bytes.starts_with(MAGIC) {
            return Err("is not a pack of this format");
        }
        if named(&Sha256::digest(bytes)) != name {
            return Err("is not what was sealed under that name");
        }
        let (records, whole) = records(bytes);
        if whole != bytes.len() {
            return Err("has a record that is not what was written");
        }
        Ok(records)
    }
}

/// What this process adds.
#[derive(Default)]
struct Writer {
    /// The pack it appends to. What is in it is found once it is sealed.
    open: Option<New>,
    /// The keys added that are not in a sealed pack this process has read.
    keys: FxHashSet<[u8; KEY]>,
    /// Whether a pack was sealed in the middle of the build.
    rolled: bool,
    /// Why nothing is added for the rest of this build, if nothing is.
    stopped: Option<String>,
    /// How many values were not added because of it.
    dropped: usize,
}

struct New {
    path: PathBuf,
    /// Locked for as long as it is ours.
    file: File,
    written: u64,
    /// Records that are not in the file yet.
    pending: Vec<u8>,
}

/// Whether a value of `RUSTD_CACHE` says there is to be no store.
pub fn is_off(value: &std::ffi::OsStr) -> bool {
    value.is_empty() || value == "off" || value == "0"
}

impl Store {
    #[cfg(test)]
    pub(super) fn for_test(dir: &Path) -> Store {
        Self::open(dir, Identity::new(b"test", "test"), Tuning { seal_at: 1, limit: None }).unwrap()
    }

    /// The store of this process: the directory `RUSTD_CACHE` names, when it names one. A
    /// directory that cannot be used is said once, and the process compiles without one.
    pub(super) fn global() -> Option<&'static Store> {
        static STORE: OnceLock<Option<Store>> = OnceLock::new();
        STORE
            .get_or_init(|| {
                let dir = std::env::var_os("RUSTD_CACHE").filter(|it| !is_off(it))?;
                let opened = Identity::current().and_then(|identity| {
                    Store::open(Path::new(&dir), identity, Tuning::from_env()?)
                });
                opened.map_err(|e| eprintln!("store: not used: {e}")).ok()
            })
            .as_ref()
    }

    fn open(dir: &Path, identity: Identity, tuning: Tuning) -> io::Result<Store> {
        let dir = StoreDir::at(dir);
        dir.claim()?;
        let store = Store {
            dir,
            identity,
            tuning,
            sealed: RwLock::default(),
            writer: Mutex::default(),
            hits: AtomicUsize::new(0),
            misses: AtomicUsize::new(0),
            corrupt: AtomicUsize::new(0),
            settling: Mutex::default(),
        };
        store.collect();
        store.refresh();
        Ok(store)
    }

    fn collect(&self) {
        if let Err(e) = self.dir.collect(self.tuning.limit) {
            eprintln!("store: garbage not collected: {e}");
        }
    }

    /// What the sealed packs hold, also after a thread panicked with it: the two maps are
    /// whole between any two statements, and a value read by them is checked against its
    /// checksum, so the worst a panic leaves is a key that is compiled again.
    fn sealed(&self) -> RwLockReadGuard<'_, Sealed> {
        self.sealed.read().unwrap_or_else(PoisonError::into_inner)
    }

    fn sealed_mut(&self) -> RwLockWriteGuard<'_, Sealed> {
        self.sealed.write().unwrap_or_else(PoisonError::into_inner)
    }

    /// The writer. After a thread panicked with it, what it was writing is given up as
    /// after a write that failed: the open pack is left to whoever seals it, which cuts it
    /// at its last whole record, and nothing more is kept until the build ends.
    fn writer(&self) -> MutexGuard<'_, Writer> {
        self.writer.lock().unwrap_or_else(|poisoned| {
            self.writer.clear_poison();
            let mut writer = poisoned.into_inner();
            writer.stop(io::Error::other("a thread panicked while it wrote to the store"));
            writer
        })
    }

    /// Reads the sealed packs that were added to the directory since the last call, by this
    /// daemon or any other, and forgets the ones that were taken out of it.
    pub(super) fn refresh(&self) {
        let Ok(names) = self.dir.packs() else { return };
        let known: FxHashSet<String> = self.sealed().packs.keys().cloned().collect();
        let names: FxHashSet<String> = names.into_iter().collect();
        let added: Vec<&String> = names.difference(&known).collect();
        let read = self.read_packs(&added);
        let gone: FxHashSet<&String> = known.difference(&names).collect();
        if read.is_empty() && gone.is_empty() {
            return;
        }
        let mut sealed = self.sealed_mut();
        // First, so that a key of a pack that went is found in the one that took it in.
        if !gone.is_empty() {
            sealed.packs.retain(|name, _| !gone.contains(name));
            sealed.index.retain(|_, place| !gone.contains(&place.pack.name));
        }
        for (pack, records) in read {
            for record in records {
                let place = Place {
                    pack: pack.clone(),
                    at: record.value.start as u64,
                    len: record.value.len() as u32,
                    checksum: record.checksum,
                };
                sealed.index.entry(record.key).or_insert(place);
            }
            sealed.packs.insert(pack.name.clone(), pack);
        }
    }

    /// Reads and checks packs, several at a time: hashing them is most of starting up.
    fn read_packs(&self, names: &[&String]) -> Vec<(Arc<Pack>, Vec<Record>)> {
        let next = AtomicUsize::new(0);
        let read = Mutex::new(Vec::new());
        let threads = std::thread::available_parallelism().map_or(1, |it| it.get());
        std::thread::scope(|scope| {
            for _ in 0..threads.min(names.len()) {
                scope.spawn(|| {
                    while let Some(name) = names.get(next.fetch_add(1, Ordering::Relaxed)) {
                        if let Some(pack) = self.read_pack(name)
                            && let Ok(mut read) = read.lock()
                        {
                            read.push(pack);
                        }
                    }
                });
            }
        });
        read.into_inner().unwrap_or_default()
    }

    /// The pack and its records, if it is what its name says. One that is not is removed.
    fn read_pack(&self, name: &str) -> Option<(Arc<Pack>, Vec<Record>)> {
        // To write as well where that is allowed, which is what Windows asks of whoever
        // sets a file's time of last use.
        let opened = self.dir.open(name, true).or_else(|_| self.dir.open(name, false));
        let mut file = match opened {
            Ok(file) => file,
            Err(e) if not_the_users(&e) => {
                self.discard(name, &e.to_string());
                return None;
            }
            // Evicted since it was listed.
            Err(_) => return None,
        };
        let mut bytes = Vec::new();
        io::Read::read_to_end(&mut file, &mut bytes).ok()?;
        match Pack::check(name, &bytes) {
            Ok(records) => {
                let (used, changed) = (AtomicBool::new(false), AtomicBool::new(false));
                Some((Arc::new(Pack { name: name.to_owned(), file, used, changed }), records))
            }
            Err(why) => {
                self.discard(name, why);
                None
            }
        }
    }

    /// Takes a pack that is not what was written out of the directory: what was in it is
    /// compiled again.
    fn discard(&self, name: &str, why: &str) {
        self.corrupt.fetch_add(1, Ordering::Relaxed);
        let removed = match std::fs::remove_file(self.dir.dir.join(name)) {
            Ok(()) => "removed".to_owned(),
            Err(e) => format!("not removed: {e}"),
        };
        eprintln!("store: {name} {why}; {removed}");
    }

    /// Runs `settle`, which ends a build's use of the store, beside what the build does
    /// next. One at a time: the one before is waited for.
    pub(super) fn settle_with(&self, settle: impl FnOnce() + Send + 'static) {
        self.settled();
        let Ok(mut settling) = self.settling.lock() else { return settle() };
        match std::thread::Builder::new().name("rustd store settle".to_owned()).spawn(settle) {
            Ok(thread) => *settling = Some(thread),
            Err(e) => eprintln!("store: what this build added is not kept: {e}"),
        }
    }

    /// Waits for what [`Self::settle_with`] started.
    pub(super) fn settled(&self) {
        let thread = self.settling.lock().ok().and_then(|mut it| it.take());
        if let Some(thread) = thread {
            _ = thread.join();
        }
    }

    /// Writes out what has been added, seals it when there is enough of it, and reads what
    /// other daemons sealed. What is not written by the time the daemon ends is compiled
    /// again by the next.
    pub(super) fn flush(&self) {
        self.settle(self.tuning.seal_at);
    }

    /// As [`Self::flush`], sealing the open pack if it has `seal_at` bytes.
    fn settle(&self, seal_at: u64) {
        let sealed = self.writer().settle(&self.dir, seal_at);
        self.mark_used();
        if sealed {
            self.collect();
        }
        self.refresh();
        let sealed = self.sealed();
        self.writer().keys.retain(|key| !sealed.index.contains_key(key));
        drop(sealed);
        let corrupt = self.corrupt.swap(0, Ordering::Relaxed);
        if corrupt != 0 {
            eprintln!("store: {corrupt} packs or values were not what was written, and are gone");
        }
    }

    /// Sets the time of last use of the packs that were read from, which is what a
    /// collection goes by.
    fn mark_used(&self) {
        let sealed = self.sealed();
        let now = SystemTime::now();
        for pack in sealed.packs.values() {
            if pack.used.swap(false, Ordering::Relaxed) {
                // Another user's pack: it stays as old as it was.
                _ = pack.file.set_modified(now);
            }
        }
    }

    /// Where the value of a key as it is on disk is. A key no sealed pack has is asked of
    /// whoever fetches packs for this process, and looked for again in what arrived.
    fn place(&self, key: &[u8; KEY]) -> Option<Place> {
        let known = || self.sealed().index.get(key).cloned();
        if let Some(place) = known() {
            return Some(place);
        }
        if !FETCH_MISSING.get().is_some_and(|fetch| fetch(key)) {
            return None;
        }
        self.refresh();
        known()
    }

    /// Whether a sealed pack has a value for the key.
    pub(super) fn has(&self, key: &[u8; KEY]) -> bool {
        self.place(&self.identity.key(key)).is_some()
    }

    /// The value of a key, if a sealed pack has it as it was written.
    pub(super) fn get(&self, key: &[u8; KEY]) -> Option<Vec<u8>> {
        let key = self.identity.key(key);
        let place = self.place(&key)?;
        let mut value = vec![0; place.len as usize];
        let read = read_at(&place.pack.file, &mut value, place.at);
        if read.is_err() || checksum(&key, &value) != place.checksum {
            self.forget(&place.pack);
            return None;
        }
        place.pack.used.store(true, Ordering::Relaxed);
        Some(value)
    }

    /// Stops reading a pack that changed after it was first read, and removes it.
    fn forget(&self, pack: &Arc<Pack>) {
        // Only the first to find it says so.
        if pack.changed.swap(true, Ordering::Relaxed) {
            return;
        }
        // The pack stays known, so that it is not read again should it not be removable.
        self.sealed_mut().index.retain(|_, place| !Arc::ptr_eq(&place.pack, pack));
        self.discard(&pack.name, "has a value that is not what was written");
    }

    /// The code of a function by what it was compiled from, counted as found or not.
    pub(super) fn lookup(&self, key: &[u8; KEY]) -> Option<Vec<u8>> {
        let found = self.get(key);
        let counted = if found.is_some() { &self.hits } else { &self.misses };
        counted.fetch_add(1, Ordering::Relaxed);
        found
    }

    /// Adds a value, unless the key has one. A value that cannot be written is not an error
    /// to the build: it is counted, and compiled again by the next.
    pub(super) fn insert(&self, key: &[u8; KEY], value: &[u8]) {
        let key = self.identity.key(key);
        if self.sealed().index.contains_key(&key) {
            return;
        }
        let Ok(len) = u32::try_from(value.len()) else { return };
        // Every thread that compiles adds here: the lock is held to put the record with the
        // others and no longer. Its checksum is worked out before, and a pack that is full
        // is hashed and sealed after.
        let record = record(&key, value, len);
        let roll_at = self.tuning.seal_at * ROLL_AFTER;
        let Some(full) = self.writer().add(&self.dir, roll_at, &key, &record) else {
            return;
        };
        let sealed = full.seal(&self.dir.dir);
        let mut writer = self.writer();
        match sealed {
            Ok(()) => writer.rolled = true,
            Err(e) => {
                writer.dropped += 1;
                writer.stop(e);
            }
        }
    }

    /// How many functions were found, and how many were not, since the last call.
    pub(super) fn take_counts(&self) -> (usize, usize) {
        (self.hits.swap(0, Ordering::Relaxed), self.misses.swap(0, Ordering::Relaxed))
    }
}

impl Writer {
    /// Adds the record of `key`, unless it was added. What comes back is the open pack once
    /// it has `roll_at` bytes, for the caller to seal: the next record opens another.
    fn add(&mut self, dir: &StoreDir, roll_at: u64, key: &[u8; KEY], record: &[u8]) -> Option<New> {
        if self.stopped.is_some() {
            self.dropped += 1;
            return None;
        }
        if self.keys.contains(key) {
            return None;
        }
        match self.append(dir, roll_at, record) {
            Ok(full) => {
                self.keys.insert(*key);
                full
            }
            Err(e) => {
                self.dropped += 1;
                self.stop(e);
                None
            }
        }
    }

    fn append(&mut self, dir: &StoreDir, roll_at: u64, record: &[u8]) -> io::Result<Option<New>> {
        let new = match &mut self.open {
            Some(new) => new,
            empty => empty.insert(New::create(&dir.dir)?),
        };
        new.pending.extend_from_slice(record);
        if new.pending.len() >= WRITE_AT {
            new.write_out()?;
        }
        Ok(if new.written >= roll_at { self.open.take() } else { None })
    }

    /// Adds nothing more until the build ends. What the open pack has on disk stays for
    /// whoever seals it.
    fn stop(&mut self, error: io::Error) {
        self.open = None;
        // Some of them were in what is now given up.
        self.keys.clear();
        eprintln!("store: nothing more is kept of this build: {error}");
        self.stopped = Some(error.to_string());
    }

    /// At the end of a build: writes out what waits, and seals the open pack if it is large
    /// enough. Returns whether a pack was sealed since the build before.
    fn settle(&mut self, dir: &StoreDir, seal_at: u64) -> bool {
        if self.stopped.is_none()
            && let Err(e) = self.seal_if_large(dir, seal_at)
        {
            self.stop(e);
        }
        // The next build tries again: what was in the way may be gone.
        if self.stopped.take().is_some() {
            eprintln!("store: {} values of this build were not kept", self.dropped);
            self.dropped = 0;
        }
        std::mem::take(&mut self.rolled)
    }

    fn seal_if_large(&mut self, dir: &StoreDir, seal_at: u64) -> io::Result<()> {
        let Some(new) = &mut self.open else { return Ok(()) };
        new.write_out()?;
        if new.written >= seal_at
            && let Some(large) = self.open.take()
        {
            large.seal(&dir.dir)?;
            self.rolled = true;
        }
        Ok(())
    }
}

impl New {
    fn create(dir: &Path) -> io::Result<New> {
        // A daemon that seals what was left open may take this one for left open before it
        // is locked, and remove it.
        for _ in 0..8 {
            let path = dir.join(format!("{}-{}.open", std::process::id(), nanos()));
            let mut options = OpenOptions::new();
            // Read when it is sealed, for the name its bytes give it.
            let options = options.read(true).write(true).create_new(true);
            let file = match private::file(options).open(&path) {
                Ok(file) => file,
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e),
            };
            if file.try_lock().is_err() || !path.exists() {
                continue;
            }
            let pending = MAGIC.to_vec();
            return Ok(New { path, file, written: 0, pending });
        }
        Err(io::Error::other("no open pack could be held"))
    }

    /// Writes the records that wait to the file. When they cannot all be written the file
    /// is cut back to what it had, so that it ends with a whole record.
    fn write_out(&mut self) -> io::Result<()> {
        if self.pending.is_empty() {
            return Ok(());
        }
        if let Err(e) = self.file.write_all(&self.pending) {
            _ = self.file.set_len(self.written);
            return Err(e);
        }
        self.written += self.pending.len() as u64;
        self.pending.clear();
        Ok(())
    }

    /// Gives the pack the name of its bytes, which is when other daemons start to read it.
    /// The bytes are hashed here, all at once and from the file, and not as they are added:
    /// adding is under the lock every thread that compiles waits for.
    fn seal(mut self, dir: &Path) -> io::Result<()> {
        self.write_out()?;
        self.file.sync_all()?;
        let mut hash = Sha256::new();
        io::Seek::seek(&mut self.file, io::SeekFrom::Start(0))?;
        io::copy(&mut self.file, &mut hash)?;
        std::fs::rename(&self.path, dir.join(named(&hash.finalize())))?;
        sync_dir(dir)
    }
}

#[cfg(windows)]
mod acl;

/// Keeping the store to the user it is of. On Unix that is the owner and the mode of the
/// directory and of each file. On Windows it is the owner and the access control list,
/// see [`acl`]: a directory is made with the list it inherits, which under the user's
/// profile lets in the user alone, and one that lets in others is refused, not mended.
mod private {
    use std::{
        fs::{File, OpenOptions},
        io,
        path::Path,
    };

    /// What makes a directory that was refused one that is taken.
    #[cfg(not(windows))]
    pub(super) const MENDED_BY: &str = "`chmod 700` it";
    #[cfg(windows)]
    pub(super) const MENDED_BY: &str =
        "`icacls DIR /inheritance:r /grant:r \"%USERNAME%:(OI)(CI)F\"` it";

    /// Opens a directory for what is asked of it by its handle.
    pub(super) fn open_dir(dir: &Path) -> io::Result<File> {
        let mut options = OpenOptions::new();
        options.read(true);
        // Windows opens a directory only when told that it may be one.
        #[cfg(windows)]
        std::os::windows::fs::OpenOptionsExt::custom_flags(&mut options, 0x0200_0000);
        options.open(dir)
    }

    /// Makes the directory and the ones above it that are missing, for the user alone.
    pub(super) fn create_dir(dir: &Path) -> io::Result<()> {
        let mut builder = std::fs::DirBuilder::new();
        builder.recursive(true);
        #[cfg(unix)]
        std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
        builder.create(dir)
    }

    /// Takes from other users the reading of a directory that is the user's: what is in a
    /// store tells what was built from it.
    pub(super) fn close(dir: &Path) -> io::Result<()> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            let mut permissions = std::fs::metadata(dir)?.permissions();
            if permissions.mode() & 0o077 != 0 {
                permissions.set_mode(permissions.mode() & !0o077);
                std::fs::set_permissions(dir, permissions)?;
            }
        }
        _ = dir;
        Ok(())
    }

    /// Has a file that is created be the user's alone to read and write.
    pub(super) fn file(options: &mut OpenOptions) -> &mut OpenOptions {
        #[cfg(unix)]
        std::os::unix::fs::OpenOptionsExt::mode(options, 0o600);
        options
    }

    /// Why what `file` is could have been written by someone other than the user this
    /// process runs as, if it could.
    #[cfg(unix)]
    pub(super) fn others_write(file: &File) -> Option<&'static str> {
        use std::os::unix::fs::MetadataExt as _;
        let Ok(meta) = file.metadata() else {
            return Some("has an owner that could not be read");
        };
        // SAFETY: `geteuid` takes nothing and cannot fail.
        let user = unsafe { libc::geteuid() };
        if meta.uid() != user {
            return Some("belongs to another user");
        }
        (meta.mode() & 0o022 != 0).then_some("can be written to by other users")
    }

    #[cfg(windows)]
    pub(super) use super::acl::others_write;

    #[cfg(not(any(unix, windows)))]
    pub(super) fn others_write(_: &File) -> Option<&'static str> {
        None
    }
}

/// The store as Cranelift asks for it: one of these per function compiled.
pub(super) struct Lookup(pub(super) &'static Store);

impl CacheKvStore for Lookup {
    fn get(&self, key: &[u8]) -> Option<Cow<'_, [u8]>> {
        let key = <&[u8; KEY]>::try_from(key).ok()?;
        self.0.lookup(key).map(Cow::Owned)
    }

    fn insert(&mut self, key: &[u8], val: Vec<u8>) {
        if let Ok(key) = <&[u8; KEY]>::try_from(key) {
            self.0.insert(key, &val);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Seals at every flush, and keeps everything.
    const EAGER: Tuning = Tuning { seal_at: 1, limit: None };

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("rustd-store-{name}-{}", std::process::id()));
        _ = std::fs::remove_dir_all(&dir);
        dir
    }

    fn identity(toolchain: &str) -> Identity {
        Identity::new(b"a build", toolchain)
    }

    fn open(dir: &Path, tuning: Tuning) -> Store {
        Store::open(dir, identity("a toolchain"), tuning).unwrap()
    }

    fn files(dir: &Path, kind: Kind) -> Vec<PathBuf> {
        let mut found: Vec<_> = StoreDir::at(dir)
            .names()
            .unwrap()
            .iter()
            .filter(|it| Kind::of(it) == Some(kind))
            .map(|it| dir.join(it))
            .collect();
        found.sort();
        found
    }

    /// A store with one sealed pack that has `[1; KEY]` and `[2; KEY]` in it.
    fn sealed(dir: &Path) -> PathBuf {
        let store = open(dir, EAGER);
        store.insert(&[1; KEY], b"one");
        store.insert(&[2; KEY], &[7; 4096]);
        store.flush();
        let packs = files(dir, Kind::Pack);
        assert_eq!(packs.len(), 1);
        packs[0].clone()
    }

    fn change(path: &Path, change: impl FnOnce(&mut Vec<u8>)) {
        let mut bytes = std::fs::read(path).unwrap();
        change(&mut bytes);
        std::fs::write(path, bytes).unwrap();
    }

    #[test]
    fn sealed_pack_is_named_by_its_bytes_and_read_back() {
        let dir = scratch("seal");
        let store = open(&dir, EAGER);
        store.insert(&[1; KEY], b"one");
        assert_eq!(store.get(&[1; KEY]), None);
        store.flush();
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        let packs = files(&dir, Kind::Pack);
        let name = packs[0].file_name().unwrap().to_str().unwrap().to_owned();
        assert_eq!(pack_name(&std::fs::read(&packs[0]).unwrap()), Some(name));
        assert!(files(&dir, Kind::Open).is_empty());
        assert!(files(&dir, Kind::Temporary).is_empty());
        assert_eq!(open(&dir, EAGER).get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn packs_filled_by_many_threads_at_once_are_each_named_by_their_bytes() {
        let dir = scratch("threads");
        let store = open(&dir, EAGER);
        let key = |thread: u8, n: u8| {
            let mut key = [thread; KEY];
            key[0] = n;
            key
        };
        // Enough that packs fill and are sealed while the other threads go on adding.
        std::thread::scope(|scope| {
            for thread in 0..8 {
                let store = &store;
                scope.spawn(move || {
                    for n in 0..100 {
                        store.insert(&key(thread, n), &[thread ^ n; 8 << 10]);
                    }
                });
            }
        });
        assert!(files(&dir, Kind::Pack).len() > 1);
        store.flush();
        assert!(files(&dir, Kind::Open).is_empty());
        for pack in files(&dir, Kind::Pack) {
            let name = pack.file_name().unwrap().to_str().unwrap().to_owned();
            assert_eq!(pack_name(&std::fs::read(&pack).unwrap()), Some(name));
        }
        let reader = open(&dir, EAGER);
        for thread in 0..8 {
            for n in 0..100 {
                let value = [thread ^ n; 8 << 10];
                assert_eq!(store.get(&key(thread, n)).as_deref(), Some(&value[..]));
                assert_eq!(reader.get(&key(thread, n)).as_deref(), Some(&value[..]));
            }
        }
        assert!(StoreDir::at(&dir).verify().unwrap().corrupt.is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_small_open_pack_stays_open_and_is_sealed_by_the_next_daemon() {
        let dir = scratch("adopt");
        let store = open(&dir, Tuning { seal_at: SEAL_AT, limit: None });
        store.insert(&[1; KEY], b"one");
        store.flush();
        assert_eq!(files(&dir, Kind::Open).len(), 1);
        drop(store);
        let next = open(&dir, EAGER);
        assert!(files(&dir, Kind::Open).is_empty());
        assert_eq!(next.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_torn_open_pack_keeps_its_whole_records() {
        let dir = scratch("torn");
        let store = open(&dir, Tuning { seal_at: SEAL_AT, limit: None });
        store.insert(&[1; KEY], b"one");
        store.insert(&[2; KEY], b"two");
        store.flush();
        drop(store);
        let left = files(&dir, Kind::Open);
        change(&left[0], |bytes| bytes.truncate(bytes.len() - 1));
        let next = open(&dir, EAGER);
        assert_eq!(next.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        assert_eq!(next.get(&[2; KEY]), None);
        let verified = StoreDir::at(&dir).verify().unwrap();
        assert_eq!((verified.packs, verified.records, verified.corrupt.len()), (1, 1, 0));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn an_older_format_is_emptied_and_what_is_not_the_stores_is_left() {
        let dir = scratch("older");
        std::fs::create_dir_all(&dir).unwrap();
        let old = dir.join(named(&[3; KEY]));
        std::fs::write(&old, b"rustdpk\x01 what the first format wrote").unwrap();
        std::fs::write(dir.join("1-2.open"), b"rustdpk\x01").unwrap();
        std::fs::write(dir.join("notes.txt"), b"not the store's").unwrap();
        assert_eq!(StoreDir::at(&dir).format(), Some(1));
        let store = open(&dir, EAGER);
        assert_eq!(StoreDir::at(&dir).format(), Some(FORMAT));
        assert!(!old.exists() && !dir.join("1-2.open").exists());
        assert!(dir.join("notes.txt").exists());
        store.insert(&[1; KEY], b"one");
        store.flush();
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_store_whose_format_was_never_all_said_is_of_none() {
        let dir = scratch("unsaid");
        std::fs::create_dir_all(&dir).unwrap();
        let begun = dir.join(format!("{VERSION_FILE}.1-2.tmp"));
        std::fs::write(&begun, b"rustd st").unwrap();
        assert_eq!(StoreDir::at(&dir).format(), None);
        let store = open(&dir, EAGER);
        assert_eq!(StoreDir::at(&dir).format(), Some(FORMAT));
        assert!(!begun.exists());
        drop(store);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_newer_format_is_refused_and_left_as_it_is() {
        let dir = scratch("newer");
        std::fs::create_dir_all(&dir).unwrap();
        let theirs = dir.join(named(&[3; KEY]));
        std::fs::write(&theirs, b"rustdpk\x09 from the future").unwrap();
        std::fs::write(dir.join(VERSION_FILE), format!("rustd store {}\n", FORMAT + 1)).unwrap();
        let refused = Store::open(&dir, identity("a toolchain"), EAGER).err().unwrap();
        assert!(refused.to_string().contains("format"), "{refused}");
        assert!(theirs.exists());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_pack_of_another_format_under_this_version_is_discarded() {
        let dir = scratch("magic");
        let pack = sealed(&dir);
        let mut bytes = std::fs::read(&pack).unwrap();
        bytes[MAGIC.len() - 1] = 1;
        let other = dir.join(named(&Sha256::digest(&bytes)));
        std::fs::write(&other, bytes).unwrap();
        let store = open(&dir, EAGER);
        assert!(!other.exists());
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn another_build_or_toolchain_does_not_find_the_value() {
        let dir = scratch("identity");
        sealed(&dir);
        for other in
            [Identity::new(b"a build", "another"), Identity::new(b"another", "a toolchain")]
        {
            let store = Store::open(&dir, other, EAGER).unwrap();
            assert_eq!(store.get(&[1; KEY]), None);
            store.insert(&[1; KEY], b"theirs");
            store.flush();
            assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"theirs"[..]));
        }
        assert_eq!(open(&dir, EAGER).get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_flipped_bit_anywhere_in_a_pack_discards_it() {
        let dir = scratch("flip");
        let len = std::fs::metadata(sealed(&dir)).unwrap().len() as usize;
        for at in [0, MAGIC.len(), MAGIC.len() + KEY + 1, MAGIC.len() + HEADER, len / 2, len - 1] {
            std::fs::remove_dir_all(&dir).unwrap();
            let pack = sealed(&dir);
            change(&pack, |bytes| bytes[at] ^= 0x10);
            let store = open(&dir, EAGER);
            assert_eq!(store.get(&[1; KEY]), None, "byte {at}");
            assert_eq!(store.get(&[2; KEY]), None, "byte {at}");
            assert!(!pack.exists(), "byte {at}");
            store.insert(&[1; KEY], b"one");
            store.flush();
            assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
            assert!(StoreDir::at(&dir).verify().unwrap().corrupt.is_empty());
        }
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_truncated_pack_is_discarded() {
        let dir = scratch("truncate");
        for keep in [0, 3, MAGIC.len(), MAGIC.len() + HEADER + 3, usize::MAX] {
            _ = std::fs::remove_dir_all(&dir);
            let pack = sealed(&dir);
            change(&pack, |bytes| bytes.truncate(keep.min(bytes.len() - 1)));
            let found = StoreDir::at(&dir).verify().unwrap();
            assert_eq!(found.corrupt.len(), 1, "{keep} bytes kept");
            let store = open(&dir, EAGER);
            assert_eq!(store.get(&[1; KEY]), None, "{keep} bytes kept");
            assert!(!pack.exists(), "{keep} bytes kept");
        }
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_pack_that_changes_after_it_was_read_is_not_trusted() {
        let dir = scratch("later");
        let pack = sealed(&dir);
        let store = open(&dir, EAGER);
        assert!(store.has(&[2; KEY]));
        change(&pack, |bytes| {
            let last = bytes.len() - 1;
            bytes[last] ^= 1;
        });
        assert_eq!(store.get(&[2; KEY]), None);
        assert!(!pack.exists());
        // What else was in it is not trusted either.
        assert_eq!(store.get(&[1; KEY]), None);
        store.insert(&[2; KEY], b"again");
        store.flush();
        assert_eq!(store.get(&[2; KEY]).as_deref(), Some(&b"again"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    fn pack_of(dir: &Path, key: u8, len: usize, age: u64) -> PathBuf {
        std::fs::create_dir_all(dir).unwrap();
        let before: FxHashSet<PathBuf> = files(dir, Kind::Pack).into_iter().collect();
        let store = open(dir, EAGER);
        store.insert(&[key; KEY], &vec![key; len]);
        store.flush();
        let new = files(dir, Kind::Pack).into_iter().find(|it| !before.contains(it)).unwrap();
        let used = SystemTime::now() - Duration::from_secs(age);
        File::options().write(true).open(&new).unwrap().set_modified(used).unwrap();
        new
    }

    #[test]
    fn the_packs_unused_the_longest_go_first() {
        let dir = scratch("lru");
        let oldest = pack_of(&dir, 1, 1000, 300);
        let middle = pack_of(&dir, 2, 1000, 200);
        let newest = pack_of(&dir, 3, 1000, 100);
        // Reading from the oldest makes it the newest.
        let store = open(&dir, EAGER);
        assert!(store.get(&[1; KEY]).is_some());
        store.flush();
        let collected = StoreDir::at(&dir).collect(Some(2500)).unwrap();
        assert_eq!((collected.evicted, collected.kept), (1, 2));
        assert!(oldest.exists() && !middle.exists() && newest.exists());
        // A daemon that has it open still reads it; the next does not find it.
        assert_eq!(store.get(&[2; KEY]).as_deref(), Some(&[2; 1000][..]));
        assert_eq!(open(&dir, EAGER).get(&[2; KEY]), None);
        let collected = StoreDir::at(&dir).collect(Some(0)).unwrap();
        assert_eq!((collected.evicted, collected.kept, collected.kept_bytes), (2, 0, 0));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_daemon_keeps_its_store_under_the_limit() {
        let dir = scratch("limit");
        let store = open(&dir, Tuning { seal_at: 1, limit: Some(5000) });
        for key in 0..20 {
            store.insert(&[key; KEY], &[key; 1000]);
            store.flush();
        }
        let stats = StoreDir::at(&dir).stats().unwrap();
        assert!(stats.pack_bytes <= 5000 && stats.packs >= 3, "{stats:?}");
        assert_eq!(store.get(&[19; KEY]).as_deref(), Some(&[19; 1000][..]));
        assert_eq!(store.get(&[0; KEY]), None);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn many_small_packs_are_made_one_with_every_key() {
        let dir = scratch("merge");
        // Written as daemons that never collect would have, so that they are all there.
        let store = StoreDir::at(&dir);
        store.claim().unwrap();
        for key in 0..SMALL_PACKS as u8 + 4 {
            let mut pack = MAGIC.to_vec();
            pack.extend(record(&identity("a toolchain").key(&[key; KEY]), &[key; 10], 10));
            store.write_whole(&named(&Sha256::digest(&pack)), &pack).unwrap();
        }
        let collected = store.collect(None).unwrap();
        assert_eq!((collected.merged, collected.kept), (SMALL_PACKS + 4, 1));
        let reader = open(&dir, EAGER);
        for key in 0..SMALL_PACKS as u8 + 4 {
            assert_eq!(reader.get(&[key; KEY]).as_deref(), Some(&[key; 10][..]));
        }
        assert!(StoreDir::at(&dir).verify().unwrap().corrupt.is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn stores_that_share_a_directory_find_what_the_others_sealed() {
        let dir = scratch("shared");
        let limit = Some(64 << 10);
        std::thread::scope(|scope| {
            for writer in 0..6u8 {
                let dir = &dir;
                scope.spawn(move || {
                    let store = open(dir, Tuning { seal_at: 1, limit });
                    for round in 0..40u8 {
                        // Half of the keys are every writer's.
                        let key = [if round % 2 == 0 { 0 } else { writer + 1 }, round];
                        let mut full = [0; KEY];
                        full[..2].copy_from_slice(&key);
                        let value = vec![round; 700 + round as usize];
                        if let Some(found) = store.get(&full) {
                            assert_eq!(found, value);
                        }
                        store.insert(&full, &value);
                        store.flush();
                    }
                });
            }
        });
        let verified = StoreDir::at(&dir).verify().unwrap();
        assert!(verified.corrupt.is_empty(), "{verified:?}");
        assert_eq!(verified.open, 0);
        let stats = StoreDir::at(&dir).stats().unwrap();
        assert!(stats.packs > 0 && stats.temporary == 0, "{stats:?}");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_file_is_written_whole_and_leaves_nothing_behind() {
        let dir = scratch("whole");
        std::fs::create_dir_all(&dir).unwrap();
        let name = named(&[5; KEY]);
        StoreDir::at(&dir).write_whole(&name, b"first").unwrap();
        StoreDir::at(&dir).write_whole(&name, b"second").unwrap();
        assert_eq!(std::fs::read(dir.join(&name)).unwrap(), b"second");
        assert!(files(&dir, Kind::Temporary).is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn what_is_left_on_the_way_to_a_name_is_removed_once_it_is_old() {
        let dir = scratch("abandoned");
        sealed(&dir);
        let left = dir.join(format!("{}.1-2.tmp", named(&[5; KEY])));
        std::fs::write(&left, b"half of a pack").unwrap();
        assert_eq!(StoreDir::at(&dir).collect(None).unwrap().abandoned, 0);
        let old = SystemTime::now() - TEMPORARY_FOR * 2;
        File::options().write(true).open(&left).unwrap().set_modified(old).unwrap();
        assert_eq!(StoreDir::at(&dir).collect(None).unwrap().abandoned, 1);
        assert!(!left.exists());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn the_start_of_a_fetched_pack_is_kept_for_a_fetch_to_go_on_from() {
        let dir = scratch("fetched");
        sealed(&dir);
        let kept = ["fetch", "zst"].map(|end| dir.join(format!("{}.{end}.tmp", named(&[5; KEY]))));
        for (left, age) in kept.iter().zip([TEMPORARY_FOR * 2, FETCHED_FOR * 2]) {
            std::fs::write(left, b"half of a pack").unwrap();
            let old = SystemTime::now() - age;
            File::options().write(true).open(left).unwrap().set_modified(old).unwrap();
        }
        assert_eq!(StoreDir::at(&dir).collect(None).unwrap().abandoned, 1);
        assert!(kept[0].exists() && !kept[1].exists());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn the_keys_a_store_says_it_holds_are_those_of_its_records() {
        let dir = scratch("keys");
        sealed(&dir);
        let store = StoreDir::at(&dir);
        let mut held = Vec::new();
        for name in store.packs().unwrap() {
            let pack = std::fs::read(dir.join(&name)).unwrap();
            held.extend(pack_keys(&name, &pack).unwrap());
            // Cut short in a value, the record it is in is not counted.
            assert_eq!(headed(&pack[..pack.len() - 1]).len(), headed(&pack).len() - 1);
        }
        assert!(!held.is_empty());
        assert_eq!(store.keys().unwrap(), held.into_iter().collect());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn names_that_are_not_the_stores_are_not_its_files() {
        for name in ["lock", "notes.txt", "1-2.open.bak", "x.open", "-.open", "version.tmp"] {
            assert!(Kind::of(name).is_none(), "{name}");
        }
        assert!(Kind::of("12-34.open") == Some(Kind::Open));
        assert!(Kind::of("version.12-34.tmp") == Some(Kind::Temporary));
        assert!(Kind::of(&format!("{}.7.partial", named(&[0; KEY]))) == Some(Kind::Temporary));
        // A pack that a pull was stopped in the middle of, and nothing else called so.
        assert!(Kind::of(&format!("{}.fetch.tmp", named(&[0; KEY]))) == Some(Kind::Temporary));
        assert!(Kind::of(&format!("{}.zst.tmp", named(&[0; KEY]))) == Some(Kind::Temporary));
        assert!(Kind::of(&format!("{}.send.tmp", named(&[0; KEY]))) == Some(Kind::Temporary));
        assert!(Kind::of("version.fetch.tmp").is_none());
        assert!(Kind::of(&format!("{}.fetched.tmp", named(&[0; KEY]))).is_none());
    }

    #[test]
    fn a_pack_says_its_format_and_its_keys_to_those_who_send_it() {
        let dir = scratch("sent");
        let pack = sealed(&dir);
        let name = pack.file_name().unwrap().to_str().unwrap();
        let mut bytes = std::fs::read(&pack).unwrap();
        assert_eq!(pack_format(&bytes), Some(FORMAT));
        assert_eq!(pack_format(b"rustdpk\x01 of the first format"), Some(1));
        assert_eq!(pack_format(b"rustdpk"), None);
        assert_eq!(pack_format(b"something else"), None);
        let keys = [1, 2].map(|key| identity("a toolchain").key(&[key; KEY]));
        assert_eq!(pack_keys(name, &bytes).unwrap(), keys);
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        assert_eq!(StoreDir::at(&dir).keys().unwrap(), keys.into_iter().collect());
        assert!(pack_keys(name, &bytes).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_file_that_arrived_in_pieces_gets_its_name_whole() {
        let dir = scratch("pieces");
        std::fs::create_dir_all(&dir).unwrap();
        let (from, to) =
            (dir.join(format!("{}.fetch.tmp", named(&[5; KEY]))), dir.join(named(&[5; KEY])));
        let mut file = File::create(&from).unwrap();
        file.write_all(b"one piece, ").unwrap();
        assert!(Kind::of(from.file_name().unwrap().to_str().unwrap()) == Some(Kind::Temporary));
        file.write_all(b"and another").unwrap();
        name_file_whole(&file, &from, &to).unwrap();
        assert_eq!(std::fs::read(&to).unwrap(), b"one piece, and another");
        assert!(files(&dir, Kind::Temporary).is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn sizes_are_read_as_people_write_them() {
        assert_eq!(parse_size("4096"), Some(4096));
        assert_eq!(parse_size("2k"), Some(2 << 10));
        assert_eq!(parse_size(" 3M "), Some(3 << 20));
        assert_eq!(parse_size("8G"), Some(8 << 30));
        assert_eq!(parse_size("G"), None);
        assert_eq!(parse_size(""), None);
        assert_eq!(parse_size("99999999999999999999G"), None);
        assert_eq!(parse_size("17179869184G"), None);
    }

    /// `/dev/full` takes no byte, as a disk with no room does.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_full_disk_stops_the_writer_for_the_build_and_no_longer() {
        let dir = scratch("full");
        let store = open(&dir, EAGER);
        let full = New {
            path: dir.join("1-1.open"),
            file: File::options().write(true).open("/dev/full").unwrap(),
            written: 0,
            pending: MAGIC.to_vec(),
        };
        store.writer.lock().unwrap().open = Some(full);
        store.insert(&[1; KEY], &vec![1; WRITE_AT]);
        store.insert(&[2; KEY], b"two");
        {
            let writer = store.writer.lock().unwrap();
            assert!(writer.stopped.as_deref().is_some_and(|it| it.contains("space")));
            assert_eq!(writer.dropped, 2);
            assert!(writer.open.is_none());
        }
        store.flush();
        assert_eq!(store.get(&[1; KEY]), None);
        store.insert(&[1; KEY], b"one");
        store.flush();
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_thread_that_panics_with_the_store_stops_the_writer_for_the_build_and_no_longer() {
        let dir = scratch("poisoned");
        let store = open(&dir, EAGER);
        store.insert(&[1; KEY], b"one");
        store.flush();
        std::thread::scope(|scope| {
            let with_the_index = scope.spawn(|| {
                let _sealed = store.sealed.write().unwrap();
                panic!("unwinds as an interrupted build does");
            });
            let with_the_writer = scope.spawn(|| {
                let _writer = store.writer.lock().unwrap();
                panic!("unwinds as an interrupted build does");
            });
            assert!(with_the_index.join().is_err() && with_the_writer.join().is_err());
        });
        assert!(store.sealed.is_poisoned() && store.writer.is_poisoned());
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        store.insert(&[2; KEY], b"two");
        assert!(!store.writer.is_poisoned());
        {
            let writer = store.writer();
            assert!(writer.stopped.as_deref().is_some_and(|it| it.contains("panicked")));
            assert_eq!(writer.dropped, 1);
        }
        store.flush();
        assert_eq!(store.get(&[2; KEY]), None);
        store.insert(&[2; KEY], b"two");
        store.flush();
        assert_eq!(store.get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        assert_eq!(store.get(&[2; KEY]).as_deref(), Some(&b"two"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(unix)]
    fn mode(path: &Path) -> u32 {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::metadata(path).unwrap().permissions().mode() & 0o777
    }

    #[cfg(unix)]
    fn chmod(path: &Path, mode: u32) {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn the_store_and_its_files_are_the_users_alone() {
        let dir = scratch("private");
        let pack = sealed(&dir);
        let store = open(&dir, Tuning { seal_at: u64::MAX, limit: None });
        store.insert(&[3; KEY], b"three");
        store.flush();
        assert_eq!(mode(&dir), 0o700);
        assert_eq!(mode(&pack), 0o600);
        assert_eq!(mode(&dir.join(VERSION_FILE)), 0o600);
        assert_eq!(mode(&files(&dir, Kind::Open)[0]), 0o600);
        drop(StoreDir::at(&dir).lock().unwrap());
        assert_eq!(mode(&dir.join(LOCK_FILE)), 0o600);
    }

    #[cfg(unix)]
    #[test]
    fn a_store_others_could_read_is_closed_to_them() {
        let dir = scratch("readable");
        std::fs::create_dir_all(&dir).unwrap();
        chmod(&dir, 0o755);
        StoreDir::at(&dir).claim().unwrap();
        assert_eq!(mode(&dir), 0o700);
    }

    #[cfg(unix)]
    #[test]
    fn a_store_others_can_write_to_is_refused() {
        for open_to in [0o720, 0o702, 0o777] {
            let dir = scratch("writable");
            sealed(&dir);
            chmod(&dir, open_to);
            let refused = Store::open(&dir, identity("a toolchain"), EAGER).err().unwrap();
            assert_eq!(refused.kind(), io::ErrorKind::PermissionDenied, "{open_to:o}");
            assert!(refused.to_string().contains("written to by other users"), "{refused}");
            assert!(StoreDir::at(&dir).verify().is_err());
            assert!(StoreDir::at(&dir).stats().is_err());
            assert!(StoreDir::at(&dir).collect(None).is_err());
            // Nothing in it was touched.
            chmod(&dir, 0o700);
            assert_eq!(files(&dir, Kind::Pack).len(), 1);
        }
    }

    #[cfg(unix)]
    #[test]
    fn a_pack_others_can_write_to_is_not_read() {
        let dir = scratch("writable-pack");
        let pack = sealed(&dir);
        chmod(&pack, 0o666);
        let found = StoreDir::at(&dir).verify().unwrap();
        assert_eq!(found.corrupt.len(), 1);
        assert!(found.corrupt[0].1.contains("written to by other users"));
        let store = open(&dir, EAGER);
        assert_eq!(store.get(&[1; KEY]), None);
        assert_eq!(store.corrupt.load(Ordering::Relaxed), 1);
        assert!(!pack.exists());
    }

    #[cfg(unix)]
    #[test]
    fn a_store_that_is_no_directory_is_refused() {
        let dir = scratch("no-directory");
        std::fs::write(&dir, b"").unwrap();
        assert!(Store::open(&dir, identity("a toolchain"), EAGER).is_err());
        std::fs::remove_file(&dir).unwrap();
    }

    /// Lets every user of the machine do `rights` to `path`, as `icacls` writes them.
    #[cfg(windows)]
    fn let_everyone(path: &Path, rights: &str) {
        let grant = format!("*S-1-1-0:{rights}");
        let done = std::process::Command::new("icacls").arg(path).args(["/grant", &grant]).output();
        assert!(done.unwrap().status.success(), "icacls {} /grant {grant}", path.display());
    }

    #[cfg(windows)]
    #[test]
    fn a_store_under_the_users_profile_is_taken() {
        let dir = scratch("acl-inherited");
        let pack = sealed(&dir);
        assert_eq!(StoreDir::at(&dir).verify().unwrap().corrupt, []);
        assert_eq!(open(&dir, EAGER).get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        // Reading is not writing: a store others can only read is still the user's.
        let_everyone(&dir, "(OI)(CI)RX");
        let_everyone(&pack, "R");
        assert_eq!(open(&dir, EAGER).get(&[1; KEY]).as_deref(), Some(&b"one"[..]));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(windows)]
    #[test]
    fn a_store_whose_list_lets_others_write_is_refused() {
        for rights in ["(OI)(CI)M", "(OI)(CI)F", "(AD)", "(WD)", "(DC)", "(WDAC)", "(WO)"] {
            let dir = scratch("acl-writable");
            sealed(&dir);
            let_everyone(&dir, rights);
            let refused = Store::open(&dir, identity("a toolchain"), EAGER).err().unwrap();
            assert_eq!(refused.kind(), io::ErrorKind::PermissionDenied, "{rights}");
            assert!(refused.to_string().contains("written to by other users"), "{refused}");
            assert!(refused.to_string().contains("icacls"), "{refused}");
            assert!(StoreDir::at(&dir).verify().is_err(), "{rights}");
            assert!(StoreDir::at(&dir).stats().is_err(), "{rights}");
            assert!(StoreDir::at(&dir).collect(None).is_err(), "{rights}");
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    #[cfg(windows)]
    #[test]
    fn a_pack_whose_list_lets_others_write_is_not_read() {
        let dir = scratch("acl-writable-pack");
        let pack = sealed(&dir);
        let_everyone(&pack, "M");
        let found = StoreDir::at(&dir).verify().unwrap();
        assert_eq!(found.corrupt.len(), 1);
        assert!(found.corrupt[0].1.contains("written to by other users"));
        let store = open(&dir, EAGER);
        assert_eq!(store.get(&[1; KEY]), None);
        assert_eq!(store.corrupt.load(Ordering::Relaxed), 1);
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// Another user's store is refused: run as root, where a directory can be given away.
    #[cfg(unix)]
    #[test]
    fn a_store_of_another_user_is_refused() {
        let dir = scratch("another-user");
        sealed(&dir);
        let path = std::ffi::CString::new(dir.as_os_str().as_encoded_bytes()).unwrap();
        // SAFETY: `path` is a string that ends in a zero and lives through the call.
        if unsafe { libc::chown(path.as_ptr(), 65534, 65534) } != 0 {
            eprintln!("skipped: this user cannot give a directory away");
            return;
        }
        let refused = Store::open(&dir, identity("a toolchain"), EAGER).err().unwrap();
        assert!(refused.to_string().contains("belongs to another user"), "{refused}");
    }

    /// A pack with two records, as it is sealed.
    fn pack() -> Vec<u8> {
        let mut pack = MAGIC.to_vec();
        pack.extend(record(&[1; KEY], b"one", 3));
        pack.extend(record(&[2; KEY], &[7; 300], 300));
        pack
    }

    #[test]
    fn no_bytes_break_the_reading_of_a_pack() {
        use super::super::fuzz;
        let seeds = vec![pack(), MAGIC.to_vec(), Vec::new()];
        let (mut whole, mut cut) = (0, 0);
        for bytes in fuzz::inputs("pack", seeds) {
            let (largest, (found, end)) = fuzz::largest_allocation(|| records(&bytes));
            assert!(largest <= fuzz::allowed(bytes.len()), "{largest} bytes for {}", bytes.len());
            assert!(end <= bytes.len());
            for record in &found {
                assert_eq!(checksum(&record.key, &bytes[record.value.clone()]), record.checksum);
            }
            // Under the name of its bytes, which whoever writes a pack can give it.
            let name = named(&Sha256::digest(&bytes));
            match Pack::check(&name, &bytes) {
                Ok(records) => {
                    assert_eq!(records.len(), found.len());
                    whole += 1;
                }
                Err(_) => cut += 1,
            }
            assert!(Pack::check(&named(&[0; 32]), &bytes).is_err());
        }
        eprintln!("pack: {whole} whole, {cut} not");
        assert!(whole > 3 && cut > 0);
    }

    #[test]
    fn no_name_breaks_the_telling_of_what_a_file_is() {
        use super::super::fuzz;
        let name = |it: &str| it.as_bytes().to_vec();
        let seeds = vec![
            name(&named(&[0xab; 32])),
            name("4242-1700000000000000000.open"),
            name(&format!("{}.4242-17.tmp", named(&[0xcd; 32]))),
            name("version.1-2.tmp"),
            name(VERSION_FILE),
            name(LOCK_FILE),
        ];
        let mut ours = 0;
        for bytes in fuzz::inputs("name", seeds) {
            let name = String::from_utf8_lossy(&bytes);
            let kind = Kind::of(&name);
            assert_eq!(kind == Some(Kind::Pack), is_pack(&name));
            // Nothing that is a path to somewhere else is the store's.
            assert!(kind.is_none() || !name.contains(['/', '\\', '\0']), "{name}");
            ours += usize::from(kind.is_some());
            _ = parse_size(&name);
        }
        assert!(ours > 5);
    }
}
