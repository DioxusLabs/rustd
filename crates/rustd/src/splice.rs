//! Answering an edit without linking again: the executable of the last full link stays as it
//! is, and the functions that changed are added to its end.
//!
//! A full link of dx writes half a gigabyte to replace a few kilobytes of code. The splice
//! writes those kilobytes: it lays the patch object out behind everything the linker loaded,
//! resolves what it refers to against the executable's symbols, and writes a jump to the new
//! code over the entry of each function the patch replaces. Whatever referred to the old
//! function, a call, a vtable or a function pointer, still arrives there and goes on to the
//! new one. Data has no entry to jump from, so a static with another value is written where
//! the old one is, when it is no larger.
//!
//! What is appended, in four segments of its own:
//!
//! 1. Read-only: the search table of the unwinder with the patch's frames added, the
//!    patch's constants and unwind tables, and the load-time relocations with the patch's
//!    added.
//! 2. Code: the patch's functions, and a stub for each import they call directly.
//! 3. Data: the patch's writable sections, an address slot for each symbol the code
//!    reaches through one, and one for the loader to fix up in place of each address a
//!    static no longer stores.
//! 4. The program headers with the new segments among them. A kernel before Linux 5.18, and
//!    qemu's user mode, tell the loader they are as far into memory as into the file
//!    whatever the headers say, so they are loaded exactly there: behind everything else,
//!    where nothing has to reach them.
//!
//! Behind those, not loaded, is what a debugger reads of the new code: see [`debug`].
//!
//! The patch holds everything that differs from the object the executable was linked from, so
//! each splice starts from the executable as the linker left it: the last one is undone
//! first. Anything the splice has no answer for is an error, and the caller links in full.
//!
//! That is the splice of an ELF executable. A wasm module is written again instead, with
//! the patch's functions in place of its own: see [`wasm`].

mod wasm;

use std::{
    fs::{File, OpenOptions},
    mem::offset_of,
    path::{Path, PathBuf},
    thread::JoinHandle,
    time::SystemTime,
};

use anyhow::{Context, bail, ensure};
use object::{
    Endianness, Object, ObjectSection, ObjectSymbol, ObjectSymbolTable, RelocationFlags,
    RelocationTarget, SectionIndex, SymbolIndex, SymbolKind, elf,
    read::elf::{ElfFile64, FileHeader, ProgramHeader},
};
use rustc_hash::{FxHashMap, FxHashSet};

mod debug;
mod macho;
mod pe;

/// The executable of the last full link, which is read on a thread of its own while the
/// daemon waits for the next edit.
pub(crate) struct Linked(JoinHandle<anyhow::Result<Baseline>>);

impl Linked {
    /// Starts reading the executable the linker just wrote at `binary` from `patch` and the
    /// rest of the link line. The patch is read here and now: the next edit writes another.
    pub(crate) fn read(binary: PathBuf, patch: &Path, object: &Path) -> Linked {
        let (patch, object) = (std::fs::read(patch), object.to_owned());
        Linked(std::thread::spawn(move || Baseline::read(binary, &patch?, &object)))
    }

    pub(crate) fn baseline(self) -> anyhow::Result<Baseline> {
        self.0.join().map_err(|_| anyhow::anyhow!("reading the executable panicked"))?
    }
}

/// An executable as the linker wrote it, and what the last splice changed of it.
pub(crate) struct Baseline {
    path: PathBuf,
    image: Executable,
    /// The functions of the patch the executable was linked with. A patch without one of
    /// them means the function is as it first was again, which the executable no longer has.
    baked: Vec<Box<[u8]>>,
    /// What the last splice wrote over, to put back before the next.
    undo: Vec<(u64, Vec<u8>)>,
    /// What the last splice left behind what the linker wrote, which the next one mostly
    /// writes again as it is.
    left: Left,
    /// What the file was when we last left it: someone else may have written it since.
    stamp: Stamp,
}

/// What a splice appended that the next may find where it is.
#[derive(Default)]
struct Left {
    /// What was appended, and where.
    appended: Option<(u64, Vec<u8>)>,
    /// The runs of what the linker wrote that are further on too.
    moved: Vec<debug::Moved>,
}

impl Left {
    /// Writes `appended` at `offset`, but for the parts that are there already.
    fn append(&self, file: &File, offset: u64, appended: &[u8]) -> std::io::Result<()> {
        const PART: usize = 1 << 16;
        let old = match &self.appended {
            Some((at, old)) if *at == offset => old.as_slice(),
            _ => &[],
        };
        let mut start = 0;
        while start < appended.len() {
            let same = |at: usize| {
                let end = (at + PART).min(appended.len());
                old.get(at..end) == Some(&appended[at..end])
            };
            if same(start) {
                start += PART;
                continue;
            }
            let mut end = start + PART;
            while end < appended.len() && !same(end) {
                end += PART;
            }
            let end = end.min(appended.len());
            write_all_at(file, &appended[start..end], offset + start as u64)?;
            start = end;
        }
        Ok(())
    }
}

/// An executable by the format it is in, which is what its splice depends on.
enum Executable {
    Elf(Image),
    MachO(macho::Image),
    Pe(pe::Image),
    Wasm(wasm::Module),
}

/// What a splice did, for the log.
pub(crate) struct Spliced {
    pub(crate) redirected: usize,
    pub(crate) appended: usize,
}

impl Baseline {
    /// Reads the executable at `path`, which was linked with `patch` ahead of `object`.
    fn read(path: PathBuf, patch: &[u8], object: &Path) -> anyhow::Result<Baseline> {
        let file = File::open(&path)?;
        let stamp = Stamp::of(&file)?;
        // SAFETY: the daemon is the one that has the link write the file, and it does not
        // start another while this reads.
        let bytes = unsafe { memmap2::Mmap::map(&file)? };
        let (image, baked) = if bytes.starts_with(b"\0asm") {
            (Executable::Wasm(wasm::Module::read(bytes.to_vec())?), wasm::defined(patch)?)
        } else {
            let image = match object::FileKind::parse(&*bytes)? {
                object::FileKind::MachO64 => Executable::MachO(macho::Image::read(&bytes)?),
                object::FileKind::Pe64 => {
                    let object = std::fs::read(object)?;
                    Executable::Pe(pe::Image::read(&bytes, &path, &[patch, &object])?)
                }
                _ => Executable::Elf(Image::read(&bytes)?),
            };
            let patch = object::File::parse(patch)?;
            let baked = patch
                .symbols()
                .filter(|it| it.is_definition() && !it.is_local())
                .filter_map(|it| it.name_bytes().ok().map(Box::from))
                .collect();
            (image, baked)
        };
        Ok(Baseline { path, image, baked, undo: Vec::new(), left: Left::default(), stamp })
    }

    pub(crate) fn is_of(&self, binary: &Path) -> bool {
        self.path == binary
    }

    /// Whether a splice leaves what a debugger reads of the executable as it was, so that
    /// it knows nothing of the code added. A PDB is a file of its own that only the linker
    /// writes.
    pub(crate) fn leaves_debug_info(&self) -> bool {
        matches!(self.image, Executable::Pe(_))
    }

    /// Brings the executable from what the linker wrote to that with `patch` in place of the
    /// functions it defines. On an error the file may be neither: it has to be linked again.
    pub(crate) fn splice(&mut self, patch: &[u8]) -> anyhow::Result<Spliced> {
        let (addition, len) = match &self.image {
            Executable::Elf(image) => {
                let patch = Patch::read(patch, image)?;
                self.has_baked(patch.replaced.iter().map(|it| it.name))?;
                (patch.place(image)?, image.len)
            }
            Executable::Pe(image) => {
                let patch = pe::Patch::read(patch, image)?;
                self.has_baked(patch.defined())?;
                (patch.place(image)?, image.len)
            }
            Executable::Wasm(module) => {
                let (bytes, spliced) = self.rewrite(module, patch)?;
                std::fs::write(&self.path, bytes)?;
                self.stamp = Stamp::of(&File::open(&self.path)?)?;
                return Ok(spliced);
            }
            Executable::MachO(image) => {
                let Baseline { path, baked, undo, stamp, .. } = self;
                return macho::splice(image, path, baked, undo, stamp, patch);
            }
        };

        let file = OpenOptions::new().read(true).write(true).open(&self.path)?;
        ensure!(Stamp::of(&file)? == self.stamp, "the executable was written by someone else");
        for (offset, bytes) in self.undo.drain(..).rev() {
            write_all_at(&file, &bytes, offset)?;
        }
        // Until this is through, nothing is known of what is behind the linker's.
        let left = std::mem::take(&mut self.left);
        left.append(&file, addition.offset, &addition.appended)?;
        write_all_at(&file, &addition.headers, addition.headers_offset)?;
        let mut end = (addition.offset + addition.appended.len() as u64)
            .max(addition.headers_offset + addition.headers.len() as u64);
        // A run the last splice copied stays where it is while nothing else is written there,
        // also when this one has no use for it: the next may.
        let mut moved = left.moved;
        moved.retain(|it| it.to >= end);
        for run in addition.described.moved {
            if !moved.contains(&run) {
                moved.retain(|it| it.to + it.len <= run.to || run.to + run.len <= it.to);
                copy_within(&file, &run)?;
                moved.push(run);
            }
        }
        for (offset, bytes) in &addition.described.written {
            write_all_at(&file, bytes, *offset)?;
            let written = *offset + bytes.len() as u64;
            moved.retain(|it| it.to + it.len <= *offset || written <= it.to);
            end = end.max(written);
        }
        end = moved.iter().map(|it| it.to + it.len).fold(end, u64::max);
        file.set_len(end.max(len))?;
        for (offset, bytes) in &addition.overwritten {
            let mut old = vec![0; bytes.len()];
            read_exact_at(&file, &mut old, *offset)?;
            self.undo.push((*offset, old));
            write_all_at(&file, bytes, *offset)?;
        }
        self.stamp = Stamp::of(&file)?;
        let appended = addition.appended.len();
        self.left = Left { appended: Some((addition.offset, addition.appended)), moved };
        Ok(Spliced { redirected: addition.redirected, appended })
    }

    /// The splice of a wasm module, which is written anew from the linker's each time.
    fn rewrite(&self, module: &wasm::Module, patch: &[u8]) -> anyhow::Result<(Vec<u8>, Spliced)> {
        let defined: FxHashSet<Box<[u8]>> = wasm::defined(patch)?.into_iter().collect();
        ensure!(
            self.baked.iter().all(|it| defined.contains(it)),
            "a function the executable was linked with a patch of is as it first was"
        );
        ensure!(
            Stamp::of(&File::open(&self.path)?)? == self.stamp,
            "the executable was written by someone else"
        );
        module.splice(patch)
    }
}

impl Baseline {
    /// Whether a patch that defines `defined` has every function of the patch the
    /// executable was linked with.
    fn has_baked<'a>(&self, defined: impl Iterator<Item = &'a [u8]>) -> anyhow::Result<()> {
        let defined: FxHashSet<&[u8]> = defined.collect();
        ensure!(
            self.baked.iter().all(|it| defined.contains(&**it)),
            "a function the executable was linked with a patch of is as it first was"
        );
        Ok(())
    }
}

#[cfg(unix)]
fn write_all_at(file: &File, bytes: &[u8], offset: u64) -> std::io::Result<()> {
    std::os::unix::fs::FileExt::write_all_at(file, bytes, offset)
}

#[cfg(unix)]
fn read_exact_at(file: &File, bytes: &mut [u8], offset: u64) -> std::io::Result<()> {
    std::os::unix::fs::FileExt::read_exact_at(file, bytes, offset)
}

#[cfg(windows)]
fn write_all_at(mut file: &File, bytes: &[u8], offset: u64) -> std::io::Result<()> {
    use std::io::{Seek as _, SeekFrom, Write as _};
    file.seek(SeekFrom::Start(offset))?;
    file.write_all(bytes)
}

#[cfg(windows)]
fn read_exact_at(mut file: &File, bytes: &mut [u8], offset: u64) -> std::io::Result<()> {
    use std::io::{Read as _, Seek as _, SeekFrom};
    file.seek(SeekFrom::Start(offset))?;
    file.read_exact(bytes)
}

/// Writes a run of the file again behind where it is.
fn copy_within(file: &File, moved: &debug::Moved) -> std::io::Result<()> {
    let mut buffer = vec![0; moved.len.min(1 << 20) as usize];
    let mut done = 0;
    while done < moved.len {
        let part = &mut buffer[..(moved.len - done).min(1 << 20) as usize];
        read_exact_at(file, part, moved.from + done)?;
        write_all_at(file, part, moved.to + done)?;
        done += part.len() as u64;
    }
    Ok(())
}

#[derive(PartialEq)]
struct Stamp {
    len: u64,
    modified: SystemTime,
}

impl Stamp {
    fn of(file: &File) -> anyhow::Result<Stamp> {
        let meta = file.metadata()?;
        Ok(Stamp { len: meta.len(), modified: meta.modified()? })
    }
}

/// The architecture an executable is of: what its instructions can reach and how the
/// relocations of its objects are numbered.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Machine {
    X86_64,
    Aarch64,
}

/// The field a relocation fills in.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Field {
    /// An address, in 8 bytes.
    Address,
    /// A distance, in 4 bytes.
    Distance,
    /// A distance, in 8 bytes.
    FarDistance,
    /// The distance of a `b` or `bl` in instructions, in 26 bits: 128 MB either way.
    Branch,
    /// The distance of an `adrp` in pages of 4 KB, in 21 bits: 4 GB either way.
    Page,
    /// What of an address `adrp` leaves out, in units of this many bits' worth of bytes:
    /// 0 for an `add`, the size of what is loaded or stored for the others.
    InPage(u8),
}

impl Machine {
    const X16: u32 = 16;

    fn of(e_machine: u16) -> Option<Machine> {
        match e_machine {
            elf::EM_X86_64 => Some(Machine::X86_64),
            elf::EM_AARCH64 => Some(Machine::Aarch64),
            _ => None,
        }
    }

    /// The relocation by which the loader adds where the program is to an address.
    fn relative(self) -> u32 {
        match self {
            Machine::X86_64 => elf::R_X86_64_RELATIVE,
            Machine::Aarch64 => elf::R_AARCH64_RELATIVE,
        }
    }

    /// Whether the loader writes the address of what another library defines for it.
    fn imports(self, r_type: u32) -> bool {
        match self {
            Machine::X86_64 => matches!(r_type, elf::R_X86_64_GLOB_DAT | elf::R_X86_64_JUMP_SLOT),
            Machine::Aarch64 => {
                matches!(r_type, elf::R_AARCH64_GLOB_DAT | elf::R_AARCH64_JUMP_SLOT)
            }
        }
    }

    fn fixup(self, r_type: u32) -> anyhow::Result<(Fixup, Field)> {
        Ok(match self {
            Machine::X86_64 => match r_type {
                elf::R_X86_64_64 => (Fixup::Absolute, Field::Address),
                elf::R_X86_64_PC32 | elf::R_X86_64_PLT32 => (Fixup::Relative, Field::Distance),
                elf::R_X86_64_GOTPCREL | elf::R_X86_64_GOTPCRELX | elf::R_X86_64_REX_GOTPCRELX => {
                    (Fixup::ThroughSlot, Field::Distance)
                }
                other => bail!("a relocation of type {other}, which only the linker handles"),
            },
            Machine::Aarch64 => match r_type {
                elf::R_AARCH64_ABS64 => (Fixup::Absolute, Field::Address),
                elf::R_AARCH64_PREL32 => (Fixup::Relative, Field::Distance),
                elf::R_AARCH64_PREL64 => (Fixup::Relative, Field::FarDistance),
                elf::R_AARCH64_CALL26 | elf::R_AARCH64_JUMP26 => (Fixup::Relative, Field::Branch),
                elf::R_AARCH64_ADR_PREL_PG_HI21 => (Fixup::Relative, Field::Page),
                elf::R_AARCH64_ADD_ABS_LO12_NC | elf::R_AARCH64_LDST8_ABS_LO12_NC => {
                    (Fixup::Relative, Field::InPage(0))
                }
                elf::R_AARCH64_LDST16_ABS_LO12_NC => (Fixup::Relative, Field::InPage(1)),
                elf::R_AARCH64_LDST32_ABS_LO12_NC => (Fixup::Relative, Field::InPage(2)),
                elf::R_AARCH64_LDST64_ABS_LO12_NC => (Fixup::Relative, Field::InPage(3)),
                elf::R_AARCH64_LDST128_ABS_LO12_NC => (Fixup::Relative, Field::InPage(4)),
                elf::R_AARCH64_ADR_GOT_PAGE => (Fixup::ThroughSlot, Field::Page),
                elf::R_AARCH64_LD64_GOT_LO12_NC => (Fixup::ThroughSlot, Field::InPage(3)),
                other => bail!("a relocation of type {other}, which only the linker handles"),
            },
        })
    }

    /// How long the shortest jump from the entry of a function to its replacement is.
    fn jump(self) -> usize {
        match self {
            // `jmp new`.
            Machine::X86_64 => 5,
            // `b new`.
            Machine::Aarch64 => 4,
        }
    }

    /// The code of a stub, and what it is aligned to. An x86-64 one is `jmp *slot(%rip)`;
    /// an AArch64 one makes an address in `x16` and branches to it.
    fn stub(self) -> (usize, u64) {
        match self {
            Machine::X86_64 => (6, 1),
            Machine::Aarch64 => (12, 4),
        }
    }

    /// Whether a call from `place` reaches `to` without a stub in between.
    fn reaches(self, to: u64, place: u64) -> bool {
        match self {
            Machine::X86_64 => true,
            Machine::Aarch64 => Field::Branch.fill(&mut [0; 4], to, place).is_ok(),
        }
    }

    /// A stub at `stub` that jumps to the address the slot at `slot` holds.
    fn stub_through(self, slot: u64, stub: u64) -> anyhow::Result<Vec<u8>> {
        Ok(match self {
            Machine::X86_64 => {
                let mut code = vec![0xff, 0x25];
                code.extend_from_slice(&relative(slot, stub + 6)?.to_le_bytes());
                code
            }
            // `adrp x16, slot`, `ldr x16, [x16, slot's low bits]`, `br x16`.
            Machine::Aarch64 => {
                let mut code = [0x9000_0000 | Self::X16, 0xf940_0210, 0xd61f_0200]
                    .map(u32::to_le_bytes)
                    .concat();
                Field::Page.fill(&mut code[..4], slot, stub)?;
                Field::InPage(3).fill(&mut code[4..8], slot, stub + 4)?;
                code
            }
        })
    }

    /// Code at `from` that goes on at `to`, where a `b` does not reach: `adrp x16, to`,
    /// `add x16, x16, to's low bits`, `br x16`. A call may change `x16` as it likes.
    fn far_jump(self, to: u64, from: u64) -> anyhow::Result<Vec<u8>> {
        ensure!(self == Machine::Aarch64, "the program is too large");
        let mut code =
            [0x9000_0000 | Self::X16, 0x9100_0210, 0xd61f_0200].map(u32::to_le_bytes).concat();
        Field::Page.fill(&mut code[..4], to, from)?;
        Field::InPage(0).fill(&mut code[4..8], to, from + 4)?;
        Ok(code)
    }

    /// What is written over the entry of a function of `size` bytes at `old` to have it go
    /// on at `new`.
    fn redirect(self, new: u64, old: u64, size: u64) -> anyhow::Result<Vec<u8>> {
        match self {
            Machine::X86_64 => {
                let mut jump = vec![0xe9];
                jump.extend_from_slice(&relative(new, old + 5)?.to_le_bytes());
                Ok(jump)
            }
            Machine::Aarch64 => {
                let mut jump = 0x1400_0000u32.to_le_bytes().to_vec();
                if Field::Branch.fill(&mut jump, new, old).is_ok() {
                    return Ok(jump);
                }
                let jump = self.far_jump(new, old)?;
                ensure!(
                    size >= jump.len() as u64,
                    "a function of {size} bytes, too short to jump {} MB from",
                    new.abs_diff(old) >> 20
                );
                Ok(jump)
            }
        }
    }
}

impl Field {
    /// Writes what the field at `place` has for `to` into its bytes.
    fn fill(self, bytes: &mut [u8], to: u64, place: u64) -> anyhow::Result<()> {
        let instruction = |bytes: &mut [u8], mask: u32, bits: u32| {
            let old = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
            bytes[..4].copy_from_slice(&(old & !mask | bits & mask).to_le_bytes());
        };
        let within = |distance: i64, bits: u32| {
            ensure!(
                distance >= -(1 << (bits - 1)) && distance < 1 << (bits - 1),
                "the program is too large"
            );
            Ok(())
        };
        match self {
            Field::Address => bytes[..8].copy_from_slice(&to.to_le_bytes()),
            Field::Distance => bytes[..4].copy_from_slice(&relative(to, place)?.to_le_bytes()),
            Field::FarDistance => bytes[..8].copy_from_slice(&to.wrapping_sub(place).to_le_bytes()),
            Field::Branch => {
                let distance = to.wrapping_sub(place) as i64;
                ensure!(distance % 4 == 0, "a branch to between two instructions");
                within(distance >> 2, 26)?;
                instruction(bytes, 0x03ff_ffff, (distance >> 2) as u32);
            }
            Field::Page => {
                let pages = ((to >> 12) as i64).wrapping_sub((place >> 12) as i64);
                within(pages, 21)?;
                let pages = pages as u32;
                instruction(bytes, 0x60ff_ffe0, (pages & 3) << 29 | (pages >> 2 & 0x7ffff) << 5);
            }
            Field::InPage(scale) => {
                let low = (to & 0xfff) as u32;
                ensure!(
                    low.is_multiple_of(1 << scale),
                    "a load of {} bytes from an address that is not a multiple of that",
                    1 << scale
                );
                instruction(bytes, 0xfff << 10, (low >> scale) << 10);
            }
        }
        Ok(())
    }

    fn len(self) -> usize {
        match self {
            Field::Address | Field::FarDistance => 8,
            _ => 4,
        }
    }
}

/// What a splice has to know of the executable. Nothing of the file is read again.
struct Image {
    len: u64,
    machine: Machine,
    header: elf::FileHeader64<Endianness>,
    segments: Vec<elf::ProgramHeader64<Endianness>>,
    /// Addresses are relative to where the program is loaded, and the loader adds that to
    /// every address stored in data.
    pie: bool,
    symbols: FxHashMap<Box<[u8]>, Named>,
    /// The address slots the loader fills with what other libraries define.
    imports: FxHashMap<Box<[u8]>, u64>,
    unwind: UnwindTable,
    /// `None` when the loader has no addresses to fix up.
    relocations: Option<LoadRelocations>,
    described: debug::Described,
}

/// What a name stands for in the executable.
enum Named {
    One(Defined),
    /// Symbols private to their objects that share the name: which one is meant is lost.
    Many,
}

#[derive(Clone, Copy)]
struct Defined {
    address: u64,
    size: u64,
    kind: SymbolKind,
    /// Where the file has its entry of the symbol table.
    entry: u64,
}

impl Defined {
    fn is(&self, other: &Defined) -> bool {
        (self.address, self.size, self.kind) == (other.address, other.size, other.kind)
    }
}

/// `.eh_frame_hdr`: the frames of the program sorted by the code they describe, which the
/// unwinder finds through a program header.
struct UnwindTable {
    segment: usize,
    address: u64,
    /// Where `.eh_frame` starts.
    frames: u64,
    /// Pairs of the start of a function and its frame, both relative to `address`.
    entries: Vec<u8>,
}

/// `.rela.dyn`, and where `.dynamic` says where it is and how long.
struct LoadRelocations {
    table: Vec<u8>,
    address_at: u64,
    size_at: u64,
    /// Whether `DT_RELR` has more of them, in a form that is not added to here.
    packed: bool,
}

impl Image {
    fn read(bytes: &[u8]) -> anyhow::Result<Image> {
        let file = ElfFile64::<Endianness>::parse(bytes)?;
        let endian = file.endian();
        let header = *file.elf_header();
        let machine =
            Machine::of(header.e_machine(endian)).filter(|_| endian == Endianness::Little);
        let machine = machine.context("an executable of an architecture nothing is added to")?;
        let pie = match header.e_type(endian) {
            elf::ET_DYN => true,
            elf::ET_EXEC => false,
            other => bail!("not an executable (type {other})"),
        };
        let segments = file.elf_program_headers().to_vec();

        let mut symbols = FxHashMap::<Box<[u8]>, Named>::default();
        let (table, _) = (file.section_by_name(".symtab").and_then(|it| it.file_range()))
            .context("the executable has no symbol table")?;
        for symbol in file.symbols() {
            if !symbol.is_definition() || symbol.section_index().is_none() {
                continue;
            }
            let name = symbol.name_bytes()?;
            let defined = Defined {
                address: symbol.address(),
                size: symbol.size(),
                kind: symbol.kind(),
                entry: table + (symbol.index().0 * size_of::<elf::Sym64<Endianness>>()) as u64,
            };
            match symbols.get_mut(name) {
                None => _ = symbols.insert(name.into(), Named::One(defined)),
                Some(Named::One(known)) if known.is(&defined) => {}
                Some(known) => *known = Named::Many,
            }
        }

        let mut imports = FxHashMap::default();
        if let (Some(relocations), Some(dynamic)) =
            (file.dynamic_relocations(), file.dynamic_symbol_table())
        {
            for (slot, relocation) in relocations {
                let RelocationFlags::Elf { r_type } = relocation.flags() else { continue };
                let RelocationTarget::Symbol(symbol) = relocation.target() else { continue };
                if machine.imports(r_type) {
                    let name = dynamic.symbol_by_index(symbol)?.name_bytes()?;
                    imports.entry(name.into()).or_insert(slot);
                }
            }
        }

        let mut image = Image {
            len: bytes.len() as u64,
            machine,
            header,
            segments,
            pie,
            symbols,
            imports,
            unwind: UnwindTable { segment: 0, address: 0, frames: 0, entries: Vec::new() },
            relocations: None,
            described: debug::Described::read(&file)?,
        };
        image.unwind = UnwindTable::read(&image, bytes)?;
        image.relocations = LoadRelocations::read(&image, bytes)?;
        ensure!(
            !image.lands_on_pads(&file)?,
            "an executable whose indirect branches have to land on `bti`"
        );
        Ok(image)
    }

    /// Whether the loader is told to fault an indirect branch that lands on anything but a
    /// `bti`: the jump written over the entry of a function is none.
    fn lands_on_pads(&self, file: &ElfFile64<'_, Endianness>) -> anyhow::Result<bool> {
        let e = Endianness::Little;
        if self.machine != Machine::Aarch64 {
            return Ok(false);
        }
        for segment in file.elf_program_headers() {
            let Some(mut notes) = segment.notes(e, file.data())? else { continue };
            while let Some(note) = notes.next()? {
                let Some(mut properties) = note.gnu_properties(e) else { continue };
                while let Some(property) = properties.next()? {
                    if property.pr_type() == elf::GNU_PROPERTY_AARCH64_FEATURE_1_AND
                        && property.data_u32(e)? & elf::GNU_PROPERTY_AARCH64_FEATURE_1_BTI != 0
                    {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    fn segments_of(&self, kind: u32) -> impl Iterator<Item = &elf::ProgramHeader64<Endianness>> {
        self.segments.iter().filter(move |it| it.p_type(Endianness::Little) == kind)
    }

    /// Where in the file the linker put what is loaded at `address`.
    fn offset_of(&self, address: u64) -> anyhow::Result<u64> {
        let e = Endianness::Little;
        self.segments_of(elf::PT_LOAD)
            .find(|it| (it.p_vaddr(e)..it.p_vaddr(e) + it.p_filesz(e)).contains(&address))
            .map(|it| it.p_offset(e) + (address - it.p_vaddr(e)))
            .with_context(|| format!("nothing of the file is loaded at {address:#x}"))
    }

    fn bytes_at<'a>(&self, bytes: &'a [u8], address: u64, len: u64) -> anyhow::Result<&'a [u8]> {
        let start = self.offset_of(address)? as usize;
        bytes.get(start..start + len as usize).context("the file ends early")
    }

    /// The first address past everything the program loads.
    fn end(&self) -> u64 {
        let e = Endianness::Little;
        self.segments_of(elf::PT_LOAD).map(|it| it.p_vaddr(e) + it.p_memsz(e)).max().unwrap_or(0)
    }

    /// Where a splice adds to the file and to memory, at `offset` and `address` or past
    /// them: as far from each other as the linker's frames are in the two. A profiler that
    /// unwinds by the file finds the frames from the unwind table by how far they are from
    /// it in memory, so the table a splice writes has to be that far from them in the file.
    fn behind(&self, offset: u64, address: u64) -> (u64, u64) {
        let e = Endianness::Little;
        let frames = self.unwind.frames;
        let holds = |it: &&elf::ProgramHeader64<Endianness>| {
            (it.p_vaddr(e)..it.p_vaddr(e) + it.p_filesz(e)).contains(&frames)
        };
        let ahead = (self.segments_of(elf::PT_LOAD).find(holds))
            .and_then(|it| it.p_vaddr(e).checked_sub(it.p_offset(e)));
        match ahead {
            Some(ahead) => {
                let address = address.max(offset + ahead);
                (address - ahead, address)
            }
            None => (offset, address),
        }
    }

    fn page(&self) -> u64 {
        let e = Endianness::Little;
        self.segments_of(elf::PT_LOAD).map(|it| it.p_align(e)).max().unwrap_or(1).max(1)
    }
}

impl UnwindTable {
    /// The encodings every linker writes the table in: a 4-byte count, and pairs of 4-byte
    /// offsets from the table's start.
    const ENCODINGS: [u8; 4] =
        [1, eh::RELATIVE | eh::SIGNED_4, eh::UNSIGNED_4, eh::TABLE_RELATIVE | eh::SIGNED_4];
    const HEADER: usize = 12;
    const ENTRY: usize = 8;

    fn read(image: &Image, bytes: &[u8]) -> anyhow::Result<UnwindTable> {
        let e = Endianness::Little;
        let (segment, header) = image
            .segments
            .iter()
            .enumerate()
            .find(|it| it.1.p_type(e) == elf::PT_GNU_EH_FRAME)
            .context("the executable has no unwind table")?;
        let address = header.p_vaddr(e);
        let table = image.bytes_at(bytes, address, header.p_filesz(e))?;
        ensure!(
            table.len() >= Self::HEADER && table[..4] == Self::ENCODINGS,
            "an unwind table in encodings we don't write"
        );
        let frames = (address + 4).wrapping_add_signed(i64::from(read_i32(&table[4..])));
        let count = u32::from_le_bytes(table[8..12].try_into()?) as usize;
        let entries = table
            .get(Self::HEADER..Self::HEADER + count * Self::ENTRY)
            .context("the unwind table ends early")?
            .to_vec();
        Ok(UnwindTable { segment, address, frames, entries })
    }

    fn len_with(&self, added: usize) -> usize {
        Self::HEADER + self.entries.len() + added * Self::ENTRY
    }

    /// The table as it is at `address`, with `added` frames given by the address of their
    /// code and their own. All of them are of code behind the program's.
    fn moved(&self, address: u64, mut added: Vec<(u64, u64)>) -> anyhow::Result<Vec<u8>> {
        added.sort_unstable();
        let mut table = Vec::with_capacity(self.len_with(added.len()));
        table.extend_from_slice(&Self::ENCODINGS);
        table.extend_from_slice(&relative(self.frames, address + 4)?.to_le_bytes());
        let count = self.entries.len() / Self::ENTRY + added.len();
        table.extend_from_slice(&u32::try_from(count)?.to_le_bytes());
        let shift = relative(self.address, address)?;
        for &field in self.entries.as_chunks().0 {
            let field =
                i32::from_le_bytes(field).checked_add(shift).context("the program is too large")?;
            table.extend_from_slice(&field.to_le_bytes());
        }
        for (code, frame) in added {
            table.extend_from_slice(&relative(code, address)?.to_le_bytes());
            table.extend_from_slice(&relative(frame, address)?.to_le_bytes());
        }
        Ok(table)
    }
}

impl LoadRelocations {
    const ENTRY: usize = size_of::<elf::Rela64<Endianness>>();
    /// The tag of the packed relative relocations, which `object` has no name for.
    const DT_RELR: u32 = 36;

    fn read(image: &Image, bytes: &[u8]) -> anyhow::Result<Option<LoadRelocations>> {
        let e = Endianness::Little;
        let Some(dynamic) = image.segments_of(elf::PT_DYNAMIC).next() else { return Ok(None) };
        let start = dynamic.p_offset(e);
        let entries = bytes
            .get(start as usize..(start + dynamic.p_filesz(e)) as usize)
            .context("the file ends early")?;
        let (entries, _) = object::slice_from_bytes::<elf::Dyn64<Endianness>>(
            entries,
            entries.len() / size_of::<elf::Dyn64<Endianness>>(),
        )
        .map_err(|()| anyhow::anyhow!("a misaligned dynamic section"))?;
        let entry = |tag: u32| {
            let at = entries.iter().position(|it| it.d_tag.get(e) == u64::from(tag))?;
            let value_at = start + (at * size_of::<elf::Dyn64<Endianness>>()) as u64 + 8;
            Some((entries[at].d_val.get(e), value_at))
        };
        let (Some((address, address_at)), Some((size, size_at))) =
            (entry(elf::DT_RELA), entry(elf::DT_RELASZ))
        else {
            return Ok(None);
        };
        let table = image.bytes_at(bytes, address, size)?.to_vec();
        let packed = entry(Self::DT_RELR).is_some();
        Ok(Some(LoadRelocations { table, address_at, size_at, packed }))
    }

    fn len_with(&self, added: usize) -> usize {
        self.table.len() + added * Self::ENTRY
    }

    /// Makes the entries of `table` for the addresses that `statics` stored those for what
    /// they store now, which `restored` has by where. An address no longer stored has its
    /// entry fix up `spare` instead; the entries a new one needs are handed back.
    fn restore(
        table: &mut [u8],
        mut statics: Vec<Defined>,
        mut restored: FxHashMap<u64, u64>,
        spare: u64,
        relative: u32,
    ) -> anyhow::Result<Vec<elf::Rela64<Endianness>>> {
        let e = Endianness::Little;
        if !statics.is_empty() {
            statics.sort_unstable_by_key(|it| it.address);
            let entries = object::slice_from_all_bytes_mut::<elf::Rela64<Endianness>>(table)
                .map_err(|()| anyhow::anyhow!("misaligned load-time relocations"))?;
            for entry in entries {
                let at = entry.r_offset.get(e);
                let before = statics.partition_point(|it| it.address <= at);
                let Some(old) = before.checked_sub(1).map(|it| statics[it]) else { continue };
                if at >= old.address + old.size {
                    continue;
                }
                ensure!(
                    entry.r_info.get(e) == u64::from(relative),
                    "a static that stored the address of an import"
                );
                match restored.remove(&at) {
                    Some(value) => entry.r_addend.set(e, value as i64),
                    None => {
                        entry.r_offset.set(e, spare);
                        entry.r_addend.set(e, 0);
                    }
                }
            }
        }
        Ok(restored
            .into_iter()
            .map(|(at, value)| elf::Rela64 {
                r_offset: object::U64::new(e, at),
                r_info: object::U64::new(e, u64::from(relative)),
                r_addend: object::I64::new(e, value as i64),
            })
            .collect())
    }
}

/// How `.eh_frame` and `.eh_frame_hdr` say an address is written (`DW_EH_PE_*`).
/// What the link that writes the executable at `path` is told besides, so that an edit can
/// be spliced into what it writes: the room Apple's linker leaves in a Mach-O header.
pub(crate) fn room(path: &Path) -> Option<String> {
    macho::room(path)
}

/// What the executable just linked at `path` is linked again with, where an edit could not
/// be spliced into it for want of that room.
pub(crate) fn short_of_room(path: &Path) -> Option<String> {
    macho::short_of_room(path)
}

mod eh {
    pub(super) const ABSOLUTE: u8 = 0x00;
    pub(super) const UNSIGNED_4: u8 = 0x03;
    pub(super) const SIGNED_4: u8 = 0x0b;
    /// From where the address is written.
    pub(super) const RELATIVE: u8 = 0x10;
    /// From the start of the search table.
    pub(super) const TABLE_RELATIVE: u8 = 0x30;
}

/// What the frames of `.eh_frame` have in common, which each refers to.
struct CommonEntry;

impl CommonEntry {
    /// How the frames of the entry at `at` write where their code starts.
    fn pointer_encoding(section: &[u8], at: usize) -> anyhow::Result<u8> {
        let mut rest = section.get(at + 8..).context("a frame of no common entry")?;
        let mut byte = || -> anyhow::Result<u8> {
            let (&first, others) = rest.split_first().context("a common entry that ends early")?;
            rest = others;
            Ok(first)
        };
        let version = byte()?;
        ensure!(version == 1 || version == 3, "a common entry of version {version}");
        let mut augmentation = Vec::new();
        loop {
            match byte()? {
                0 => break,
                letter => augmentation.push(letter),
            }
        }
        let mut leb = || -> anyhow::Result<()> {
            while byte()? & 0x80 != 0 {}
            Ok(())
        };
        // The alignment of code and of data, the register of the return address, and the
        // length of what the augmentation adds.
        for _ in 0..4 {
            leb()?;
        }
        ensure!(augmentation.first() == Some(&b'z'), "a common entry without augmentation");
        for letter in &augmentation[1..] {
            match letter {
                b'R' => return byte(),
                b'L' => _ = byte()?,
                b'S' | b'B' => {}
                // The personality routine: an encoding and then an address written in it.
                b'P' => {
                    let len = match byte()? & 0x0f {
                        0x00 | 0x04 | 0x0c => 8,
                        0x03 | 0x0b => 4,
                        0x02 | 0x0a => 2,
                        other => bail!("a personality routine encoded as {other:#x}"),
                    };
                    for _ in 0..len {
                        byte()?;
                    }
                }
                other => bail!("a common entry augmented with {:?}", *other as char),
            }
        }
        Ok(eh::ABSOLUTE)
    }
}

/// A patch object, and what of the executable it needs.
struct Patch<'a> {
    file: ElfFile64<'a, Endianness>,
    /// The sections that are loaded, by the segment they go to.
    sections: [Vec<SectionIndex>; 3],
    /// What each symbol a relocation refers to stands for.
    targets: FxHashMap<SymbolIndex, Target>,
    /// The symbols the code reaches through an address slot of ours, in the order of the
    /// slots.
    slots: Vec<SymbolIndex>,
    /// What the code calls directly and may not reach, in the order of their stubs: the
    /// imports, and where a call reaches only so far, what the executable defines.
    stubs: Vec<SymbolIndex>,
    /// How many addresses the data stores, each of which the loader has to fix up.
    stored: usize,
    frames: usize,
    /// The functions and statics it defines, with what the executable has under the name.
    replaced: Vec<Replaced<'a>>,
    /// The statics among them that go where the executable has them, by where the patch does.
    in_place: FxHashMap<SectionIndex, Vec<InPlace>>,
}

#[derive(Clone, Copy)]
enum Segment {
    Read = 0,
    Code = 1,
    Data = 2,
}

impl Segment {
    const ALL: [Segment; 3] = [Segment::Read, Segment::Code, Segment::Data];

    fn flags(self) -> u32 {
        match self {
            Segment::Read => elf::PF_R,
            Segment::Code => elf::PF_R | elf::PF_X,
            Segment::Data => elf::PF_R | elf::PF_W,
        }
    }
}

#[derive(Clone, Copy)]
enum Target {
    /// At an offset in a section of the patch.
    Ours(SectionIndex, u64),
    /// A section of the patch, where what is meant is as far in as the relocation adds.
    Section(SectionIndex),
    /// At an address of the executable.
    Theirs(u64),
    /// In another library: the loader writes its address to the slot.
    Import(u64),
}

struct Replaced<'a> {
    name: &'a [u8],
    section: SectionIndex,
    offset: u64,
    size: u64,
    /// `None` for what the executable does not have.
    old: Option<Defined>,
}

/// A static of the patch that is written over the executable's.
#[derive(Clone, Copy)]
struct InPlace {
    /// Where its section has it.
    offset: u64,
    size: u64,
    old: Defined,
}

impl InPlace {
    fn holds(&self, offset: u64) -> bool {
        (self.offset..self.offset + self.size).contains(&offset)
    }
}

/// How a relocation of the patch gets its value.
enum Fixup {
    /// The address itself.
    Absolute,
    /// Where it is from the code: a distance, or the parts of one.
    Relative,
    /// Where a slot that holds the address is from the code.
    ThroughSlot,
}

impl Fixup {
    fn of(relocation: &object::Relocation, machine: Machine) -> anyhow::Result<(Fixup, Field)> {
        let RelocationFlags::Elf { r_type } = relocation.flags() else {
            bail!("a relocation that is not ELF's")
        };
        machine.fixup(r_type)
    }
}

impl<'a> Patch<'a> {
    const SLOT: usize = 8;
    /// What a table of the executable is given to grow into before what follows it moves.
    const ROOM: u64 = 1 << 20;

    fn read(bytes: &'a [u8], image: &Image) -> anyhow::Result<Patch<'a>> {
        let file = ElfFile64::<Endianness>::parse(bytes)?;
        let mut patch = Patch {
            file,
            sections: Default::default(),
            targets: FxHashMap::default(),
            slots: Vec::new(),
            stubs: Vec::new(),
            stored: 0,
            frames: 0,
            replaced: Vec::new(),
            in_place: FxHashMap::default(),
        };
        for section in patch.file.sections() {
            let object::SectionFlags::Elf { sh_flags } = section.flags() else { continue };
            if sh_flags & u64::from(elf::SHF_ALLOC) == 0 {
                continue;
            }
            ensure!(sh_flags & u64::from(elf::SHF_TLS) == 0, "the patch has thread-local data");
            let segment = if sh_flags & u64::from(elf::SHF_EXECINSTR) != 0 {
                Segment::Code
            } else if sh_flags & u64::from(elf::SHF_WRITE) != 0 {
                Segment::Data
            } else {
                Segment::Read
            };
            patch.sections[segment as usize].push(section.index());
            if section.name_bytes()? == b".eh_frame" {
                patch.frames += Self::frames_in(section.data()?, 0)?.len();
            }
        }
        let loaded: FxHashSet<SectionIndex> = patch.sections.iter().flatten().copied().collect();
        let code: FxHashSet<SectionIndex> =
            patch.sections[Segment::Code as usize].iter().copied().collect();

        for symbol in patch.file.symbols() {
            if !symbol.is_definition() || symbol.is_local() {
                continue;
            }
            let name = symbol.name_bytes()?;
            let section = symbol.section_index().context("a symbol in no section")?;
            let old = match image.symbols.get(name) {
                None => None,
                Some(Named::One(old))
                    if old.kind == SymbolKind::Text && code.contains(&section) =>
                {
                    ensure!(
                        old.size >= image.machine.jump() as u64,
                        "{} is too short to jump from",
                        String::from_utf8_lossy(name)
                    );
                    Some(*old)
                }
                Some(Named::One(old))
                    if old.kind == SymbolKind::Data && !code.contains(&section) =>
                {
                    let new = InPlace { offset: symbol.address(), size: symbol.size(), old: *old };
                    patch.fits(&new, section, image).with_context(|| {
                        format!("the static {} has another value", String::from_utf8_lossy(name))
                    })?;
                    patch.in_place.entry(section).or_default().push(new);
                    Some(*old)
                }
                Some(_) => bail!(
                    "the patch replaces {}, which is not one function or static",
                    String::from_utf8_lossy(name)
                ),
            };
            patch.replaced.push(Replaced {
                name,
                section,
                offset: symbol.address(),
                size: symbol.size(),
                old,
            });
        }
        let named: Vec<SymbolIndex> = (patch.described())
            .flat_map(|section| section.relocations())
            .filter_map(|(_, relocation)| match relocation.target() {
                RelocationTarget::Symbol(index) => Some(index),
                _ => None,
            })
            .collect();
        for index in named {
            let section = patch.file.symbol_by_index(index)?.section_index();
            if section.is_some_and(|it| loaded.contains(&it)) && !patch.targets.contains_key(&index)
            {
                let target = patch.target(index, image, &loaded)?;
                patch.targets.insert(index, target);
            }
        }
        let (mut slots, mut stubs) = (FxHashSet::default(), FxHashSet::default());
        for section in patch.file.sections().filter(|it| loaded.contains(&it.index())) {
            for (_, relocation) in section.relocations() {
                let RelocationTarget::Symbol(index) = relocation.target() else {
                    bail!("a relocation against no symbol")
                };
                let target = match patch.targets.get(&index) {
                    Some(target) => *target,
                    None => {
                        let target = patch.target(index, image, &loaded)?;
                        patch.targets.insert(index, target);
                        target
                    }
                };
                match (Fixup::of(&relocation, image.machine)?, target) {
                    ((Fixup::Absolute, _), Target::Import(_)) => {
                        bail!("data that stores the address of an import")
                    }
                    ((Fixup::Absolute, _), _) => patch.stored += 1,
                    ((Fixup::Relative, _), Target::Import(_))
                    | ((Fixup::Relative, Field::Branch), Target::Theirs(_)) => {
                        if stubs.insert(index) {
                            patch.stubs.push(index);
                        }
                    }
                    ((Fixup::ThroughSlot, _), Target::Import(_)) => {}
                    ((Fixup::ThroughSlot, _), _) => {
                        if slots.insert(index) {
                            patch.slots.push(index);
                        }
                    }
                    ((Fixup::Relative, _), _) => {}
                }
            }
        }

        Ok(patch)
    }

    /// Whether a static can go where the executable has the one it replaces: what refers to
    /// it there is not looked for.
    fn fits(&self, new: &InPlace, section: SectionIndex, image: &Image) -> anyhow::Result<()> {
        let e = Endianness::Little;
        let old = &new.old;
        ensure!(new.size <= old.size, "that is larger: {} bytes after {}", new.size, old.size);
        let section = self.file.section_by_index(section)?;
        // What a type is aligned to divides its size, and where its section has it.
        let align = (new.offset | new.size | section.align().max(1)).isolate_lowest_one();
        ensure!(old.address.is_multiple_of(align), "that may be aligned to {align}");
        let segment = image
            .segments_of(elf::PT_LOAD)
            .find(|it| {
                let start = it.p_vaddr(e);
                start <= old.address && old.address + new.size <= start + it.p_filesz(e)
            })
            .context("that the file has no bytes for")?;
        let object::SectionFlags::Elf { sh_flags } = section.flags() else { bail!("no flags") };
        ensure!(
            sh_flags & u64::from(elf::SHF_WRITE) == 0 || segment.p_flags(e) & elf::PF_W != 0,
            "that is written to, where the old one is not"
        );
        Ok(())
    }

    fn target(
        &self,
        index: SymbolIndex,
        image: &Image,
        loaded: &FxHashSet<SectionIndex>,
    ) -> anyhow::Result<Target> {
        let symbol = self.file.symbol_by_index(index)?;
        if let Some(section) = symbol.section_index() {
            ensure!(loaded.contains(&section), "a reference to a section that is not loaded");
            return Ok(match symbol.kind() {
                SymbolKind::Section => Target::Section(section),
                _ => Target::Ours(section, symbol.address()),
            });
        }
        let name = symbol.name_bytes()?;
        let shown = || String::from_utf8_lossy(name);
        ensure!(symbol.is_undefined(), "{} is neither defined nor undefined", shown());
        match image.symbols.get(name) {
            Some(Named::One(Defined { kind: SymbolKind::Tls, .. })) => {
                bail!("{} is thread-local", shown())
            }
            Some(Named::One(defined)) => Ok(Target::Theirs(defined.address)),
            Some(Named::Many) => bail!("{} names several things in the executable", shown()),
            None => match image.imports.get(name) {
                Some(slot) => Ok(Target::Import(*slot)),
                None => bail!("{} is not in the executable", shown()),
            },
        }
    }

    /// The frames in an `.eh_frame` section loaded at `address`: where the code of each
    /// starts, and where the frame is.
    fn frames_in(section: &[u8], address: u64) -> anyhow::Result<Vec<(u64, u64)>> {
        let early = "an unwind table that ends early";
        let u32_at = |at: usize| -> anyhow::Result<u32> {
            let bytes = section.get(at..at + 4).context(early)?;
            Ok(u32::from_le_bytes(bytes.try_into()?))
        };
        let mut found = Vec::new();
        let mut at = 0;
        while at < section.len() {
            let len = u32_at(at)? as usize;
            if len == 0 {
                break;
            }
            ensure!(len != u32::MAX as usize, "an unwind table in the 64-bit format");
            // A frame says how far back its common entry is; a common entry says zero.
            let back = u32_at(at + 4)? as usize;
            if back != 0 {
                let common = (at + 4).checked_sub(back).context("a frame of no common entry")?;
                let start = at + 8;
                let begins = match CommonEntry::pointer_encoding(section, common)? {
                    eh::ABSOLUTE => {
                        let bytes = section.get(start..start + 8).context(early)?;
                        u64::from_le_bytes(bytes.try_into()?)
                    }
                    encoding if encoding == eh::RELATIVE | eh::SIGNED_4 => (address + start as u64)
                        .wrapping_add_signed(i64::from(u32_at(start)? as i32)),
                    other => bail!("frames whose addresses are encoded as {other:#x}"),
                };
                found.push((begins, address + at as u64));
            }
            at += 4 + len;
        }
        Ok(found)
    }

    /// Lays the patch out behind the executable and gives everything in it its address.
    fn place(&self, image: &Image) -> anyhow::Result<Addition> {
        let e = Endianness::Little;
        let page = image.page();
        let machine = image.machine;
        let (stub_len, stub_align) = machine.stub();
        let (offset, base) =
            image.behind(image.len.next_multiple_of(page), image.end().next_multiple_of(page));
        let relocations = image.relocations.as_ref().filter(|_| image.pie);
        ensure!(!image.pie || relocations.is_some(), "an executable the loader fixes nothing in");
        let fixed_up = if image.pie { self.stored + self.slots.len() } else { 0 };

        // Where everything goes, as offsets from `base`.
        let mut end = 0u64;
        let mut reserve = |len: usize, align: u64| {
            let start = end.next_multiple_of(align);
            end = start + len as u64;
            start
        };
        let mut placed = FxHashMap::default();
        let mut extents = [(0, 0); 3];
        let headers_len = (image.segments.len() + Segment::ALL.len() + 1)
            * size_of::<elf::ProgramHeader64<Endianness>>();
        let (mut unwind_at, mut relocations_at) = (0, 0);
        let (mut stubs_at, mut slots_at, mut spare_at) = (0, 0, 0);
        for segment in Segment::ALL {
            let start = reserve(0, page);
            // The two tables of the executable first, each with room behind it, so that
            // they are where the last splice has them whatever the patch is.
            if let Segment::Read = segment {
                unwind_at = reserve(image.unwind.len_with(self.frames), 4);
                relocations_at =
                    reserve(relocations.map_or(0, |it| it.len_with(fixed_up)), Self::ROOM);
                reserve(0, Self::ROOM);
            }
            for &index in &self.sections[segment as usize] {
                let section = self.file.section_by_index(index)?;
                placed.insert(index, reserve(section.size() as usize, section.align().max(1)));
            }
            match segment {
                Segment::Read => {}
                Segment::Code => stubs_at = reserve(self.stubs.len() * stub_len, stub_align),
                Segment::Data => {
                    slots_at = reserve(self.slots.len() * Self::SLOT, 8);
                    spare_at = reserve(if self.in_place.is_empty() { 0 } else { Self::SLOT }, 8);
                }
            }
            extents[segment as usize] = (start, reserve(0, 1));
        }
        // The headers go where their place in memory is their place in the file, further
        // by what the first segment is: past the other three in both.
        let first = image.segments_of(elf::PT_LOAD).next().context("nothing is loaded")?;
        let ahead = first.p_vaddr(e).checked_sub(first.p_offset(e));
        let ahead = ahead
            .filter(|it| it.is_multiple_of(page))
            .context("a first segment loaded before where the file has it")?;
        let headers_at =
            (offset + end).max((base + end).saturating_sub(ahead)).next_multiple_of(page) - offset;
        let headers_address = offset + headers_at + ahead;
        let mut appended = vec![0u8; end as usize];

        // A static written in place is where the executable has it: its section is added
        // as a whole, with a copy of it that nothing may use. Code says how far its field is
        // from what it means in what it adds, so a section alone does not tell which static.
        let address = |target: Target, added: i64, exact: bool| -> anyhow::Result<u64> {
            let (section, at) = match target {
                Target::Ours(section, at) => (section, at),
                Target::Section(section) => (section, 0),
                Target::Theirs(address) => return Ok(address.wrapping_add_signed(added)),
                Target::Import(slot) => return Ok(slot.wrapping_add_signed(added)),
            };
            let in_place = self.in_place.get(&section).map_or(&[][..], |it| it);
            let found = match target {
                Target::Section(_) if exact => {
                    in_place.iter().find(|it| it.holds(added as u64)).map(|it| (it, added as u64))
                }
                Target::Section(_) => {
                    let near = |it: &InPlace| {
                        (it.offset as i64 - 8..(it.offset + it.size) as i64).contains(&added)
                    };
                    ensure!(
                        !in_place.iter().any(near),
                        "code that refers to a static through its section"
                    );
                    None
                }
                _ => in_place.iter().find(|it| it.holds(at)).map(|it| (it, at)),
            };
            Ok(match (found, target) {
                (Some((it, at)), Target::Section(_)) => it.old.address + (at - it.offset),
                (Some((it, at)), _) => {
                    (it.old.address + (at - it.offset)).wrapping_add_signed(added)
                }
                (None, _) => (base + placed[&section] + at).wrapping_add_signed(added),
            })
        };
        let slot_of: FxHashMap<SymbolIndex, u64> = (self.slots.iter().copied())
            .zip((0..).map(|at| base + slots_at + at * Self::SLOT as u64))
            .collect();
        let stub_of: FxHashMap<SymbolIndex, u64> = (self.stubs.iter().copied())
            .zip((0..).map(|at| base + stubs_at + at * stub_len as u64))
            .collect();

        // The addresses stored in data, which the loader moves with the program.
        let mut fixed = Vec::with_capacity(fixed_up);
        let mut store = |appended: &mut [u8], at: u64, value: u64| {
            appended[(at - base) as usize..][..8].copy_from_slice(&value.to_le_bytes());
            if image.pie {
                fixed.push(elf::Rela64 {
                    r_offset: object::U64::new(e, at),
                    r_info: object::U64::new(e, u64::from(machine.relative())),
                    r_addend: object::I64::new(e, value as i64),
                });
            }
        };

        let mut overwritten = Vec::new();
        // The addresses the statics written in place store, by where.
        let mut restored = FxHashMap::default();
        let mut frames = Vec::with_capacity(self.frames);
        for section in self.file.sections() {
            let Some(&start) = placed.get(&section.index()) else { continue };
            let data = section.data()?;
            appended[start as usize..][..data.len()].copy_from_slice(data);
            let in_place = self.in_place.get(&section.index()).map_or(&[][..], |it| it);
            let code = self.sections[Segment::Code as usize].contains(&section.index());
            let mut values: Vec<Vec<u8>> = in_place
                .iter()
                .map(|it| match data.get(it.offset as usize..(it.offset + it.size) as usize) {
                    Some(value) => value.to_vec(),
                    None => vec![0; it.size as usize],
                })
                .collect();
            for (at, relocation) in section.relocations() {
                let RelocationTarget::Symbol(index) = relocation.target() else { continue };
                let target = self.targets[&index];
                if let Some(which) = in_place.iter().position(|it| it.holds(at)) {
                    let within = (at - in_place[which].offset) as usize;
                    let (Fixup::Absolute, _) = Fixup::of(&relocation, machine)? else {
                        bail!("a static that stores a distance")
                    };
                    let value = address(target, relocation.addend(), true)?;
                    let field = values[which].get_mut(within..within + 8);
                    field
                        .context("an address past its static")?
                        .copy_from_slice(&value.to_le_bytes());
                    restored.insert(in_place[which].old.address + within as u64, value);
                    continue;
                }
                let place = base + start + at;
                let (fixup, field) = Fixup::of(&relocation, machine)?;
                let to = match (fixup, target) {
                    (Fixup::Absolute, _) => {
                        let value = address(target, relocation.addend(), true)?;
                        store(&mut appended, place, value);
                        continue;
                    }
                    (Fixup::Relative, Target::Import(_)) => {
                        stub_of[&index].wrapping_add_signed(relocation.addend())
                    }
                    (Fixup::Relative, _) | (Fixup::ThroughSlot, Target::Import(_)) => {
                        let to = address(target, relocation.addend(), !code)?;
                        match stub_of.get(&index) {
                            Some(&stub)
                                if field == Field::Branch && !machine.reaches(to, place) =>
                            {
                                ensure!(relocation.addend() == 0, "a far branch into a function");
                                stub
                            }
                            _ => to,
                        }
                    }
                    (Fixup::ThroughSlot, _) => {
                        slot_of[&index].wrapping_add_signed(relocation.addend())
                    }
                };
                let bytes = appended[(place - base) as usize..].get_mut(..field.len());
                field.fill(bytes.context("a relocation past its section")?, to, place)?;
            }
            if section.name_bytes()? == b".eh_frame" {
                let relocated = &appended[start as usize..][..data.len()];
                frames.extend(Self::frames_in(relocated, base + start)?);
            }
            for (new, value) in in_place.iter().zip(values) {
                overwritten.push((image.offset_of(new.old.address)?, value));
            }
        }
        for (&index, &slot) in &slot_of {
            store(&mut appended, slot, address(self.targets[&index], 0, true)?);
        }
        for (&index, &stub) in &stub_of {
            let code = match self.targets[&index] {
                Target::Import(slot) => machine.stub_through(slot, stub)?,
                Target::Theirs(address) => machine.far_jump(address, stub)?,
                Target::Ours(..) | Target::Section(_) => continue,
            };
            appended[(stub - base) as usize..][..stub_len].copy_from_slice(&code);
        }

        let mut redirected = 0;
        for replaced in &self.replaced {
            let Some(old) = replaced.old.filter(|it| it.kind == SymbolKind::Text) else { continue };
            let new = base + placed[&replaced.section] + replaced.offset;
            let jump = machine.redirect(new, old.address, old.size).with_context(|| {
                format!("{} cannot be jumped from", String::from_utf8_lossy(replaced.name))
            })?;
            overwritten.push((image.offset_of(old.address)?, jump));
            // Its symbol names the new code, for whoever reads a backtrace.
            let named = [new.to_le_bytes(), replaced.size.to_le_bytes()].concat();
            overwritten
                .push((old.entry + offset_of!(elf::Sym64<Endianness>, st_value) as u64, named));
            redirected += 1;
        }

        let unwind = image.unwind.moved(base + unwind_at, frames)?;
        appended[unwind_at as usize..][..unwind.len()].copy_from_slice(&unwind);
        if let Some(relocations) = relocations {
            let table = &mut appended[relocations_at as usize..];
            let old = relocations.table.len();
            table[..old].copy_from_slice(&relocations.table);
            ensure!(
                self.in_place.is_empty() || !relocations.packed,
                "a static with another value, where addresses are fixed up from a packed table"
            );
            let statics = self.in_place.values().flatten().map(|it| it.old).collect();
            let spare = base + spare_at;
            let relative = image.machine.relative();
            fixed.extend(LoadRelocations::restore(
                &mut table[..old],
                statics,
                restored,
                spare,
                relative,
            )?);
            let added = object::bytes_of_slice(&fixed);
            table[old..][..added.len()].copy_from_slice(added);
            let len = (old + added.len()) as u64;
            overwritten
                .push((relocations.address_at, (base + relocations_at).to_le_bytes().to_vec()));
            overwritten.push((relocations.size_at, len.to_le_bytes().to_vec()));
        }

        // The program headers, with the ones that moved pointing here and the new segments.
        let mut segments = image.segments.clone();
        let point_to =
            |header: &mut elf::ProgramHeader64<Endianness>, at: u64, address: u64, len: u64| {
                header.p_offset.set(e, offset + at);
                header.p_vaddr.set(e, address);
                header.p_paddr.set(e, address);
                header.p_filesz.set(e, len);
                header.p_memsz.set(e, len);
            };
        let point = |header: &mut elf::ProgramHeader64<Endianness>, at: u64, len: u64| {
            point_to(header, at, base + at, len)
        };
        point(&mut segments[image.unwind.segment], unwind_at, unwind.len() as u64);
        if let Some(header) = segments.iter_mut().find(|it| it.p_type(e) == elf::PT_PHDR) {
            point_to(header, headers_at, headers_address, headers_len as u64);
        }
        let loaded = |flags: u32| elf::ProgramHeader64::<Endianness> {
            p_type: object::U32::new(e, elf::PT_LOAD),
            p_flags: object::U32::new(e, flags),
            p_offset: object::U64::new(e, 0),
            p_vaddr: object::U64::new(e, 0),
            p_paddr: object::U64::new(e, 0),
            p_filesz: object::U64::new(e, 0),
            p_memsz: object::U64::new(e, 0),
            p_align: object::U64::new(e, page),
        };
        for segment in Segment::ALL {
            let (start, end) = extents[segment as usize];
            let mut header = loaded(segment.flags());
            point(&mut header, start, end - start);
            segments.push(header);
        }
        let mut header = loaded(elf::PF_R);
        point_to(&mut header, headers_at, headers_address, headers_len as u64);
        segments.push(header);
        let headers = object::bytes_of_slice(&segments).to_vec();
        let headers_offset = offset + headers_at;
        let described = self.describe(
            &image.described,
            machine,
            headers_offset + headers.len() as u64,
            |target, added| address(target, added, false),
        )?;
        let mut header = image.header;
        if let Some((at, count)) = described.headers {
            header.e_shoff.set(e, at);
            header.e_shnum.set(e, count);
        }
        header.e_phoff.set(e, offset + headers_at);
        header.e_phnum.set(e, u16::try_from(segments.len())?);
        overwritten.push((0, object::bytes_of(&header).to_vec()));

        Ok(Addition {
            offset,
            appended,
            headers_offset,
            headers,
            overwritten,
            redirected,
            described,
        })
    }
}

/// What a splice writes.
struct Addition {
    /// Where in the file `appended` goes: behind what the linker wrote.
    offset: u64,
    appended: Vec<u8>,
    /// The program headers, which may be far behind the rest: nothing is written between.
    headers_offset: u64,
    headers: Vec<u8>,
    /// What changes of the file the linker wrote, by where it is.
    overwritten: Vec<(u64, Vec<u8>)>,
    redirected: usize,
    /// What a debugger reads of it, behind the headers.
    described: debug::Tail,
}

fn read_i32(bytes: &[u8]) -> i32 {
    i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// The distance from `from` to `to`, where the code has four bytes for it.
fn relative(to: u64, from: u64) -> anyhow::Result<i32> {
    i32::try_from(to.wrapping_sub(from) as i64).context("the program is too large")
}

#[cfg(test)]
mod tests {
    use super::{Field, Machine};

    fn words(code: &[u8]) -> Vec<u32> {
        code.chunks(4).map(|it| u32::from_le_bytes(it.try_into().unwrap())).collect()
    }

    /// What `as` and `ld` write for the same instructions at the same addresses.
    #[test]
    fn aarch64_instructions() {
        let machine = Machine::Aarch64;
        let far = machine.far_jump(0x1235_5678, 0x10000).unwrap();
        assert_eq!(words(&far), [0xb009_1a30, 0x9119_e210, 0xd61f_0200]);
        let stub = machine.stub_through(0x7ff8, 0x1000c).unwrap();
        assert_eq!(words(&stub), [0xf0ff_ffb0, 0xf947_fe10, 0xd61f_0200]);
        assert_eq!(words(&machine.redirect(0x7ff_ff00, 0x10018, 4).unwrap()), [0x15ff_bfba]);
        let mut call = 0x9400_0000u32.to_le_bytes();
        Field::Branch.fill(&mut call, 0x400, 0x1001c).unwrap();
        assert_eq!(words(&call), [0x97ff_c0f9]);
        let mut load = 0x7940_0001u32.to_le_bytes();
        Field::InPage(1).fill(&mut load, 0x7ff8, 0x10024).unwrap();
        assert_eq!(words(&load), [0x795f_f001]);
    }

    /// A `b` reaches 128 MB: past that the jump is the long one, where it fits.
    #[test]
    fn aarch64_reach() {
        let machine = Machine::Aarch64;
        let (old, last) = (0x10000u64, 0x10000 + (128 << 20) - 4);
        assert!(machine.reaches(last, old) && !machine.reaches(last + 4, old));
        assert!(machine.reaches(0, 128 << 20) && !machine.reaches(0, (128 << 20) + 4));
        assert_eq!(machine.redirect(last, old, 4).unwrap().len(), 4);
        assert_eq!(machine.redirect(last + 4, old, 12).unwrap().len(), 12);
        assert!(machine.redirect(last + 4, old, 8).is_err());
        assert!(machine.redirect(old + (5 << 30), old, 64).is_err());
        assert!(Field::InPage(3).fill(&mut [0; 4], 0x7ffc, 0).is_err());
        // A distance of 8 bytes has room for what one of 4 turns down.
        let (to, place, mut distance) = (0x10000u64, 0x10000 + (5 << 30), [0; 8]);
        assert!(Field::Distance.fill(&mut distance, to, place).is_err());
        Field::FarDistance.fill(&mut distance, to, place).unwrap();
        assert_eq!(i64::from_le_bytes(distance), -(5 << 30));
        assert_eq!(Field::FarDistance.len(), 8);
    }
}
