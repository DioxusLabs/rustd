//! The splice into a Mach-O executable for AArch64.
//!
//! What differs from ELF is where things have to be. The loader wants `__LINKEDIT` to be the
//! last segment and the signature to be the last of it, and the kernel runs no page the
//! signature has no hash of. So the patch goes where `__LINKEDIT` was, in two segments of
//! its own, and `__LINKEDIT` is written again behind them:
//!
//! 1. `__RUSTD_TEXT`, read and run: the patch's constants and functions, and a stub for
//!    each call that is out of a branch's reach.
//! 2. `__RUSTD_DATA`, read and written: the patch's writable sections and those that store
//!    addresses, and an address slot for each symbol the code reaches through one.
//! 3. `__LINKEDIT`: as the linker wrote it but for the addresses the loader moves with the
//!    program, which are encoded again, and for the signature, which keeps the hashes of
//!    the pages that are as they were.
//!
//! The tables of the unwinder stay in `__TEXT`, the only segment the loader of older systems
//! looks for them in: the table with the patch's functions added and the frames of the
//! program with the patch's behind them are written over them and the room the linker is
//! told to leave ahead of them, up to the end of the segment.
//!
//! The kernel remembers the signature of a file it has run, so the executable is not
//! written where it is: a copy is, which the file system makes without copying where it
//! can, and takes the place of the executable when it is whole.

use std::{
    fs::{File, OpenOptions},
    path::Path,
};

use anyhow::{Context, bail, ensure};
use object::{
    Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget, SectionFlags,
    SectionIndex, SymbolIndex, SymbolKind, macho,
};
use rustc_hash::{FxHashMap, FxHashSet};
use sha2::{Digest, Sha256};

use super::{Spliced, Stamp};

/// What segments are aligned to on AArch64.
const PAGE: u64 = 0x4000;
const HEADER: usize = size_of::<macho::MachHeader64<object::LittleEndian>>();
const SEGMENT: usize = size_of::<macho::SegmentCommand64<object::LittleEndian>>();
const SECTION: usize = size_of::<macho::Section64<object::LittleEndian>>();
const NLIST: usize = size_of::<macho::Nlist64<object::LittleEndian>>();

/// The section of zeros Apple's linker is told to put ahead of the tables of the unwinder,
/// for them to grow into.
const ROOM_FOR_TABLES: &[u8] = b"__rustd_room\0\0\0\0";

fn u32_at(bytes: &[u8], at: usize) -> anyhow::Result<u32> {
    let field = bytes.get(at..at + 4).context("the file ends early")?;
    Ok(u32::from_le_bytes(field.try_into()?))
}

fn u64_at(bytes: &[u8], at: usize) -> anyhow::Result<u64> {
    let field = bytes.get(at..at + 8).context("the file ends early")?;
    Ok(u64::from_le_bytes(field.try_into()?))
}

fn put32(bytes: &mut [u8], at: usize, value: u32) {
    bytes[at..at + 4].copy_from_slice(&value.to_le_bytes());
}

fn put64(bytes: &mut [u8], at: usize, value: u64) {
    bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
}

fn uleb(bytes: &[u8], at: &mut usize) -> anyhow::Result<u64> {
    let (mut value, mut shift) = (0u64, 0);
    loop {
        let byte = *bytes.get(*at).context("a number that ends early")?;
        *at += 1;
        value |= u64::from(byte & 0x7f).checked_shl(shift).context("a number too large")?;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

fn push_uleb(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        out.push(if value == 0 { byte } else { byte | 0x80 });
        if value == 0 {
            return;
        }
    }
}

/// What a splice has to know of the executable. Nothing of the file is read again but the
/// pages a splice writes to, for their hashes.
pub(super) struct Image {
    /// The header and the load commands.
    commands: Vec<u8>,
    /// Where the first section starts in the file: the load commands end before it.
    room: usize,
    segments: Vec<Segment>,
    /// Where `commands` has what refers into `__LINKEDIT`.
    at: Commands,
    symbols: FxHashMap<Box<[u8]>, Named>,
    imports: FxHashMap<Box<[u8]>, Import>,
    unwind: Table,
    frames: Table,
    /// The addresses from where the tables of the unwinder may be written to where `__TEXT`
    /// ends, and where `commands` has the header of the room the linker left ahead of them.
    tables: (u64, u64),
    room_for_tables: Option<usize>,
    /// The addresses the loader adds where the program is loaded to, in order.
    rebases: Vec<u64>,
    /// `__LINKEDIT` up to the signature.
    linkedit: Vec<u8>,
    signature: Signature,
}

struct Segment {
    address: u64,
    size: u64,
    offset: u64,
    file_size: u64,
    writable: bool,
}

#[derive(Default)]
struct Commands {
    linkedit: usize,
    symbols: usize,
    indirect: usize,
    fixups: usize,
    signature: usize,
    /// The commands that have one offset into `__LINKEDIT` and its length.
    data: Vec<usize>,
}

/// A section the unwinder finds by its name.
#[derive(Default)]
struct Table {
    /// Where `commands` has its header.
    header: usize,
    address: u64,
    bytes: Vec<u8>,
}

enum Named {
    One(Defined),
    /// Symbols private to their objects that share the name: which one is meant is lost.
    Many,
}

#[derive(Clone, Copy, PartialEq)]
struct Defined {
    address: u64,
    /// As far as the next symbol or the end of the section: no symbol has a size here.
    size: u64,
    kind: SymbolKind,
    /// Where the file has its entry of the symbol table.
    entry: u64,
}

/// What another library defines, by how the executable reaches it.
#[derive(Clone, Copy, Default)]
struct Import {
    /// The address slot the loader fills when it loads the program.
    slot: Option<u64>,
    /// The code that jumps to it.
    stub: Option<u64>,
}

/// The signature the linker made: a directory of one hash for each page of the file.
struct Signature {
    /// The directory up to its hashes.
    directory: Vec<u8>,
    hashes: Vec<u8>,
}

impl Signature {
    const PAGE: usize = 0x1000;
    const HASH: usize = 32;
    /// A blob of blobs that holds one, the directory.
    const WRAPPER: usize = 20;
    const BLOBS: u32 = 0xfade_0cc0;
    const DIRECTORY: u32 = 0xfade_0c02;
    /// Where the directory says how long it is, how many hashes it has, and of how much.
    const LENGTH: usize = 4;
    const SLOTS: usize = 28;
    const LIMIT: usize = 32;

    fn read(blob: &[u8]) -> anyhow::Result<Signature> {
        let be = |bytes: &[u8], at: usize| -> anyhow::Result<u32> {
            let field = bytes.get(at..at + 4).context("a signature that ends early")?;
            Ok(u32::from_be_bytes(field.try_into()?))
        };
        let foreign = "a signature that is not the linker's";
        ensure!(be(blob, 0)? == Self::BLOBS && be(blob, 8)? == 1 && be(blob, 12)? == 0, foreign);
        let directory = blob.get(be(blob, 16)? as usize..).context(foreign)?;
        ensure!(be(directory, 0)? == Self::DIRECTORY, foreign);
        let (hashes, special, slots) =
            (be(directory, 16)? as usize, be(directory, 24)?, be(directory, Self::SLOTS)? as usize);
        // Hashes of 32 bytes, SHA-256, of pages of 4 KB.
        let shape = directory.get(36..40).context(foreign)?;
        ensure!(special == 0 && shape[0] == 32 && shape[1] == 2 && shape[3] == 12, foreign);
        Ok(Signature {
            directory: directory.get(..hashes).context(foreign)?.to_vec(),
            hashes: directory.get(hashes..hashes + slots * Self::HASH).context(foreign)?.to_vec(),
        })
    }

    /// How long the signature of a file is that has `limit` bytes before it.
    fn len(&self, limit: u64) -> usize {
        let pages = (limit as usize).div_ceil(Self::PAGE);
        (Self::WRAPPER + self.directory.len() + pages * Self::HASH).next_multiple_of(16)
    }

    /// The signature of `file`, whose first `kept` bytes are what the linker wrote but for
    /// `dirty`, and `added` after them.
    fn of(
        &self,
        file: &File,
        kept: u64,
        dirty: &[(u64, Vec<u8>)],
        added: &[u8],
    ) -> anyhow::Result<Vec<u8>> {
        let limit = kept + added.len() as u64;
        let kept = kept as usize / Self::PAGE;
        let mut hashes =
            self.hashes.get(..kept * Self::HASH).context("a short signature")?.to_vec();
        let mut page = vec![0; Self::PAGE];
        let pages: FxHashSet<usize> = (dirty.iter())
            .flat_map(|(at, bytes)| {
                *at as usize / Self::PAGE..=(*at as usize + bytes.len().max(1) - 1) / Self::PAGE
            })
            .filter(|page| *page < kept)
            .collect();
        for index in pages {
            super::read_exact_at(&file, &mut page, (index * Self::PAGE) as u64)?;
            hashes[index * Self::HASH..][..Self::HASH].copy_from_slice(&Sha256::digest(&page));
        }
        for page in added.chunks(Self::PAGE) {
            hashes.extend_from_slice(&Sha256::digest(page));
        }

        let mut directory = self.directory.clone();
        let length = u32::try_from(directory.len() + hashes.len())?;
        directory[Self::LENGTH..][..4].copy_from_slice(&length.to_be_bytes());
        let slots = (hashes.len() / Self::HASH) as u32;
        directory[Self::SLOTS..][..4].copy_from_slice(&slots.to_be_bytes());
        let limit = u32::try_from(limit).context("an executable of more than 4 GB")?;
        directory[Self::LIMIT..][..4].copy_from_slice(&limit.to_be_bytes());
        let mut signature = Vec::with_capacity(self.len(u64::from(limit)));
        for field in [Self::BLOBS, Self::WRAPPER as u32 + length, 1, 0, Self::WRAPPER as u32] {
            signature.extend_from_slice(&field.to_be_bytes());
        }
        signature.extend_from_slice(&directory);
        signature.extend_from_slice(&hashes);
        signature.resize(self.len(u64::from(limit)), 0);
        Ok(signature)
    }
}

/// The opcodes that say which addresses the loader moves (`REBASE_OPCODE_*`).
struct Rebases;

impl Rebases {
    fn read(stream: &[u8], segments: &[Segment]) -> anyhow::Result<Vec<u64>> {
        let mut found = Vec::new();
        let (mut at, mut address) = (0, 0u64);
        let mut rebase = |address: &mut u64, times: u64, skip: u64| {
            for _ in 0..times {
                found.push(*address);
                *address = address.wrapping_add(8 + skip);
            }
        };
        while let Some(&byte) = stream.get(at) {
            at += 1;
            let immediate = u64::from(byte & 0x0f);
            match byte & 0xf0 {
                macho::REBASE_OPCODE_DONE => break,
                macho::REBASE_OPCODE_SET_TYPE_IMM => {
                    ensure!(
                        immediate == u64::from(macho::REBASE_TYPE_POINTER),
                        "code the loader fixes up"
                    );
                }
                macho::REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB => {
                    let segment =
                        segments.get(immediate as usize).context("a fixup in no segment")?;
                    address = segment.address + uleb(stream, &mut at)?;
                }
                macho::REBASE_OPCODE_ADD_ADDR_ULEB => {
                    address = address.wrapping_add(uleb(stream, &mut at)?)
                }
                macho::REBASE_OPCODE_ADD_ADDR_IMM_SCALED => address += immediate * 8,
                macho::REBASE_OPCODE_DO_REBASE_IMM_TIMES => rebase(&mut address, immediate, 0),
                macho::REBASE_OPCODE_DO_REBASE_ULEB_TIMES => {
                    rebase(&mut address, uleb(stream, &mut at)?, 0);
                }
                macho::REBASE_OPCODE_DO_REBASE_ADD_ADDR_ULEB => {
                    rebase(&mut address, 1, uleb(stream, &mut at)?);
                }
                macho::REBASE_OPCODE_DO_REBASE_ULEB_TIMES_SKIPPING_ULEB => {
                    let times = uleb(stream, &mut at)?;
                    rebase(&mut address, times, uleb(stream, &mut at)?);
                }
                other => bail!("a fixup of kind {other:#x}"),
            }
        }
        found.sort_unstable();
        Ok(found)
    }

    /// The opcodes for `addresses`, which are in order, by the first address of each segment.
    fn written(addresses: &[u64], segments: &[u64]) -> anyhow::Result<Vec<u8>> {
        let mut stream = vec![macho::REBASE_OPCODE_SET_TYPE_IMM | macho::REBASE_TYPE_POINTER];
        let mut rest = addresses;
        while let Some(&first) = rest.first() {
            let segment = segments.partition_point(|it| *it <= first).checked_sub(1);
            let segment = segment.filter(|it| *it < 16).context("an address in no segment")?;
            let end = segments.get(segment + 1).copied().unwrap_or(u64::MAX);
            let run = (rest.iter().zip(0..))
                .take_while(|(it, nth)| **it == first + nth * 8 && **it < end)
                .count();
            stream.push(macho::REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB | segment as u8);
            push_uleb(&mut stream, first - segments[segment]);
            stream.push(macho::REBASE_OPCODE_DO_REBASE_ULEB_TIMES);
            push_uleb(&mut stream, run as u64);
            rest = &rest[run..];
        }
        stream.push(macho::REBASE_OPCODE_DONE);
        stream.resize(stream.len().next_multiple_of(8), 0);
        Ok(stream)
    }
}

impl Image {
    pub(super) fn read(bytes: &[u8]) -> anyhow::Result<Image> {
        ensure!(
            u32_at(bytes, 0)? == macho::MH_MAGIC_64 && u32_at(bytes, 4)? == macho::CPU_TYPE_ARM64,
            "not an AArch64 executable"
        );
        ensure!(u32_at(bytes, 12)? == macho::MH_EXECUTE, "not an executable");
        let count = u32_at(bytes, 16)?;
        let commands =
            bytes.get(..HEADER + u32_at(bytes, 20)? as usize).context("the file ends early")?;

        let mut segments = Vec::new();
        // The address, size and flags of each, and which the indirect symbols start at.
        let mut sections = Vec::new();
        let mut at = Commands::default();
        let (mut unwind, mut frames) = (Table::default(), Table::default());
        let mut room_for_tables = None;
        let mut room = bytes.len();
        let mut command = HEADER;
        for _ in 0..count {
            let size = u32_at(commands, command + 4)? as usize;
            match u32_at(commands, command)? {
                macho::LC_SEGMENT_64 => {
                    let name = &commands[command + 8..command + 24];
                    // Whichever comes last has to be it.
                    at.linkedit = if name.starts_with(b"__LINKEDIT\0") { command } else { 0 };
                    let segment = Segment {
                        address: u64_at(commands, command + 24)?,
                        size: u64_at(commands, command + 32)?,
                        offset: u64_at(commands, command + 40)?,
                        file_size: u64_at(commands, command + 48)?,
                        writable: u32_at(commands, command + 60)? & macho::VM_PROT_WRITE != 0,
                    };
                    for nth in 0..u32_at(commands, command + 64)? as usize {
                        let header = command + SEGMENT + nth * SECTION;
                        let (address, len) =
                            (u64_at(commands, header + 32)?, u64_at(commands, header + 40)?);
                        let offset = u32_at(commands, header + 48)? as usize;
                        let flags = u32_at(commands, header + 64)?;
                        if offset != 0 && len != 0 {
                            room = room.min(offset);
                        }
                        let table = match &commands[header..header + 16] {
                            b"__unwind_info\0\0\0" => Some(&mut unwind),
                            b"__eh_frame\0\0\0\0\0\0" => Some(&mut frames),
                            ROOM_FOR_TABLES => {
                                room_for_tables = Some(header);
                                None
                            }
                            _ => None,
                        };
                        if let Some(table) = table {
                            let content = bytes.get(offset..offset + len as usize);
                            let bytes = content.context("the file ends early")?.to_vec();
                            *table = Table { header, address, bytes };
                        }
                        let indirect = u32_at(commands, header + 68)?;
                        let stub = u32_at(commands, header + 72)?;
                        sections.push((address, len, flags, indirect, stub, header));
                    }
                    segments.push(segment);
                }
                macho::LC_SYMTAB => at.symbols = command,
                macho::LC_DYSYMTAB => at.indirect = command,
                macho::LC_DYLD_INFO | macho::LC_DYLD_INFO_ONLY => at.fixups = command,
                macho::LC_CODE_SIGNATURE => at.signature = command,
                macho::LC_FUNCTION_STARTS | macho::LC_DATA_IN_CODE => at.data.push(command),
                macho::LC_DYLD_CHAINED_FIXUPS | macho::LC_DYLD_EXPORTS_TRIE => {
                    bail!("an executable whose addresses are fixed up in chains")
                }
                macho::LC_LOAD_DYLINKER
                | macho::LC_UUID
                | macho::LC_BUILD_VERSION
                | macho::LC_VERSION_MIN_MACOSX
                | macho::LC_SOURCE_VERSION
                | macho::LC_MAIN
                | macho::LC_LOAD_DYLIB
                | macho::LC_LOAD_WEAK_DYLIB
                | macho::LC_RPATH
                | macho::LC_DYLD_ENVIRONMENT => {}
                other => bail!("a load command of kind {other:#x}"),
            }
            command += size;
        }
        ensure!(command == commands.len(), "load commands of another length than the header says");
        let present = [at.linkedit, at.symbols, at.indirect, at.fixups, at.signature];
        ensure!(
            present.iter().all(|it| *it != 0),
            "an executable without symbols, fixups or a signature, or with segments behind `__LINKEDIT`"
        );
        ensure!(
            !unwind.bytes.is_empty() && !frames.bytes.is_empty(),
            "the executable has no unwind tables"
        );
        let text = segments
            .iter()
            .find(|it| (it.address..it.address + it.file_size).contains(&unwind.address))
            .context("`__unwind_info` is in no segment")?;
        let end = text.address + text.file_size;
        let room_at = room_for_tables.map(|it| u64_at(commands, it + 32)).transpose()?;
        let start =
            room_at.unwrap_or(u64::MAX).min(unwind.address).min(frames.address).next_multiple_of(8);
        let tables = [Some(unwind.header), Some(frames.header), room_for_tables];
        ensure!(
            start >= text.address
                && frames.address + frames.bytes.len() as u64 <= end
                && sections.iter().all(|&(address, len, .., header)| {
                    tables.contains(&Some(header)) || address + len <= start || address >= end
                }),
            "the tables of the unwinder are not the last of their segment"
        );

        let linkedit = segments.last().context("no segments")?;
        ensure!(linkedit.offset.is_multiple_of(PAGE), "`__LINKEDIT` is not at a page of the file");
        let signed = u32_at(commands, at.signature + 8)? as usize;
        let signature = bytes.get(signed..).context("the file ends early")?;
        ensure!(
            signature.len() == u32_at(commands, at.signature + 12)? as usize
                && signed >= linkedit.offset as usize,
            "the signature is not the end of the file"
        );
        let signature = Signature::read(signature)?;
        let linkedit_at = linkedit.offset as usize;
        let content = bytes[linkedit_at..signed].to_vec();

        let (rebases, len) =
            (u32_at(commands, at.fixups + 8)? as usize, u32_at(commands, at.fixups + 12)? as usize);
        let stream = bytes.get(rebases..rebases + len).context("the file ends early")?;
        let rebases = Rebases::read(stream, &segments)?;

        let table = u32_at(commands, at.symbols + 8)? as usize;
        let names = bytes
            .get(u32_at(commands, at.symbols + 16)? as usize..)
            .context("the file ends early")?;
        let name = |entry: usize| -> anyhow::Result<&[u8]> {
            let name =
                names.get(u32_at(bytes, entry)? as usize..).context("a symbol of no name")?;
            Ok(name.split(|it| *it == 0).next().unwrap_or_default())
        };
        let mut defined = Vec::new();
        for nth in 0..u32_at(commands, at.symbols + 12)? as usize {
            let entry = table + nth * NLIST;
            let kind = *bytes.get(entry + 4).context("the file ends early")?;
            if kind & macho::N_STAB != 0 || kind & macho::N_TYPE != macho::N_SECT {
                continue;
            }
            let section = usize::from(bytes[entry + 5]).checked_sub(1);
            let &(start, len, flags, ..) =
                section.and_then(|it| sections.get(it)).context("a symbol in no section")?;
            let kind = match flags & macho::SECTION_TYPE {
                macho::S_THREAD_LOCAL_REGULAR..=macho::S_THREAD_LOCAL_INIT_FUNCTION_POINTERS => {
                    SymbolKind::Tls
                }
                _ if flags
                    & (macho::S_ATTR_PURE_INSTRUCTIONS | macho::S_ATTR_SOME_INSTRUCTIONS)
                    != 0 =>
                {
                    SymbolKind::Text
                }
                _ => SymbolKind::Data,
            };
            defined.push((u64_at(bytes, entry + 8)?, start + len, kind, entry));
        }
        let mut starts: Vec<u64> = defined.iter().map(|it| it.0).collect();
        starts.sort_unstable();
        starts.dedup();
        let mut symbols = FxHashMap::<Box<[u8]>, Named>::default();
        for (address, section_end, kind, entry) in defined {
            let next = starts.get(starts.partition_point(|it| *it <= address));
            let end = next.map_or(section_end, |next| section_end.min(*next));
            let defined =
                Defined { address, size: end.saturating_sub(address), kind, entry: entry as u64 };
            match symbols.get_mut(name(entry)?) {
                None => _ = symbols.insert(name(entry)?.into(), Named::One(defined)),
                Some(Named::One(known)) if *known == Defined { entry: known.entry, ..defined } => {}
                Some(known) => *known = Named::Many,
            }
        }

        let mut imports = FxHashMap::<Box<[u8]>, Import>::default();
        let indirect = u32_at(commands, at.indirect + 56)? as usize;
        for &(address, len, flags, first, stub, _) in &sections {
            let each = match flags & macho::SECTION_TYPE {
                macho::S_NON_LAZY_SYMBOL_POINTERS => 8,
                macho::S_SYMBOL_STUBS if stub != 0 => u64::from(stub),
                _ => continue,
            };
            for nth in 0..len / each {
                let symbol = u32_at(bytes, indirect + (first as usize + nth as usize) * 4)?;
                if symbol & (macho::INDIRECT_SYMBOL_LOCAL | macho::INDIRECT_SYMBOL_ABS) != 0 {
                    continue;
                }
                let entry = table + symbol as usize * NLIST;
                if *bytes.get(entry + 4).context("the file ends early")? & macho::N_TYPE
                    != macho::N_UNDF
                {
                    continue;
                }
                let import = imports.entry(name(entry)?.into()).or_default();
                let at = Some(address + nth * each);
                match each {
                    8 if flags & macho::SECTION_TYPE == macho::S_NON_LAZY_SYMBOL_POINTERS => {
                        import.slot = at
                    }
                    _ => import.stub = at,
                }
            }
        }

        Ok(Image {
            commands: commands.to_vec(),
            room,
            segments,
            at,
            symbols,
            imports,
            unwind,
            frames,
            tables: (start, end),
            room_for_tables,
            rebases,
            linkedit: content,
            signature,
        })
    }

    fn linkedit(&self) -> &Segment {
        &self.segments[self.segments.len() - 1]
    }

    /// Where the program starts: the unwinder's table counts from here.
    fn base(&self) -> anyhow::Result<u64> {
        let text = self.segments.iter().find(|it| it.offset == 0 && it.file_size != 0);
        Ok(text.context("no segment has the header")?.address)
    }

    /// Where in the file the linker put what is loaded at `address`.
    fn offset_of(&self, address: u64) -> anyhow::Result<u64> {
        (self.segments.iter())
            .find(|it| (it.address..it.address + it.file_size).contains(&address))
            .map(|it| it.offset + (address - it.address))
            .with_context(|| format!("nothing of the file is loaded at {address:#x}"))
    }
}

/// How `__eh_frame` says an address is written (`DW_EH_PE_*`).
struct Pointer {
    at: usize,
    len: usize,
    /// From where it is written, so it changes when that does.
    relative: bool,
    /// Whether it is where the code of a frame starts, and then where the frame is.
    frame: Option<usize>,
}

impl Pointer {
    fn encoded(encoding: u8, at: usize, frame: Option<usize>) -> anyhow::Result<Pointer> {
        let len = match encoding & 0x0f {
            0x00 | 0x04 | 0x0c => 8,
            0x03 | 0x0b => 4,
            other => bail!("frames whose addresses are encoded as {other:#x}"),
        };
        Ok(Pointer { at, len, relative: encoding & 0x70 == 0x10, frame })
    }

    fn value(&self, section: &[u8]) -> anyhow::Result<i64> {
        Ok(match self.len {
            4 => i64::from(u32_at(section, self.at)? as i32),
            _ => u64_at(section, self.at)? as i64,
        })
    }

    /// The addresses `section` has: of the code of each frame, of what its code throws
    /// to, and of the personality routine of each common entry.
    fn all(section: &[u8]) -> anyhow::Result<Vec<Pointer>> {
        let mut found = Vec::new();
        // How the frames of a common entry write addresses of code and of landing pads.
        let mut common = FxHashMap::<usize, (u8, Option<u8>)>::default();
        let mut at = 0;
        while at + 4 <= section.len() {
            let len = u32_at(section, at)? as usize;
            if len == 0 {
                break;
            }
            ensure!(len != u32::MAX as usize, "an unwind table in the 64-bit format");
            let back = u32_at(section, at + 4)? as usize;
            if back == 0 {
                let mut next = at + 9;
                let augmentation: Vec<u8> =
                    section[next..].iter().copied().take_while(|it| *it != 0).collect();
                next += augmentation.len() + 1;
                // The alignment of code and of data, the register of the return address,
                // and the length of what the augmentation adds.
                for _ in 0..3 {
                    uleb(section, &mut next)?;
                }
                let (mut code, mut pads) = (0, None);
                if augmentation.first() == Some(&b'z') {
                    uleb(section, &mut next)?;
                    for letter in &augmentation[1..] {
                        let encoding =
                            *section.get(next).context("a common entry that ends early")?;
                        match letter {
                            b'R' => code = encoding,
                            b'L' => pads = Some(encoding),
                            b'P' => {
                                let pointer = Pointer::encoded(encoding, next + 1, None)?;
                                next += pointer.len;
                                found.push(pointer);
                            }
                            other => bail!("a common entry augmented with {:?}", *other as char),
                        }
                        next += 1;
                    }
                }
                common.insert(at, (code, pads));
            } else {
                let entry = (at + 4).checked_sub(back).and_then(|it| common.get(&it));
                let &(code, pads) = entry.context("a frame of no common entry")?;
                let start = Pointer::encoded(code, at + 8, Some(at))?;
                let mut next = start.at + 2 * start.len;
                found.push(start);
                if let Some(pads) = pads {
                    uleb(section, &mut next)?;
                    let pad = Pointer::encoded(pads, next, None)?;
                    // Nothing is written for code that throws to nowhere.
                    if pad.value(section)? != 0 {
                        found.push(pad);
                    }
                }
            }
            at += 4 + len;
        }
        Ok(found)
    }
}

/// The table the unwinder looks a function up in (`__unwind_info`), with entries added for
/// `frames`: where the code of each starts and where `__eh_frame` has its frame, both in
/// order and behind all the table has. The functions end at `end`.
fn unwind_table(old: &[u8], frames: &[(u32, u32)], end: u32) -> anyhow::Result<Vec<u8>> {
    const INDEX: usize = 12;
    /// How many entries a page of the second level is given: it has to fit in 4 KB.
    const ENTRIES: usize = 500;
    /// "Look in `__eh_frame`", which the offset of the frame is added to.
    const DWARF: u32 = 0x0300_0000;
    ensure!(u32_at(old, 0)? == 1, "an unwind table of another version");
    let (index, count) = (u32_at(old, 20)? as usize, u32_at(old, 24)? as usize);
    ensure!(count != 0, "an unwind table of no functions");
    let entries =
        old.get(index..index + count * INDEX).context("an unwind table that ends early")?;
    // The last entry is of no page: it says where the functions end, and the landing pads.
    let (pages, last) = entries.split_at((count - 1) * INDEX);

    let mut table = old.to_vec();
    table.resize(table.len().next_multiple_of(4), 0);
    let added = frames.chunks(ENTRIES);
    let mut second = table.len() + (count + added.len()) * INDEX;
    let index = u32::try_from(table.len())?;
    put32(&mut table, 20, index);
    put32(&mut table, 24, u32::try_from(count + added.len())?);
    table.extend_from_slice(pages);
    for page in added.clone() {
        for field in [page[0].0, u32::try_from(second)?, u32_at(last, 8)?] {
            table.extend_from_slice(&field.to_le_bytes());
        }
        second += 8 + page.len() * 8;
    }
    for field in [end, 0, u32_at(last, 8)?] {
        table.extend_from_slice(&field.to_le_bytes());
    }
    for page in added {
        // A page of the regular kind, whose entries start 8 bytes in.
        table.extend_from_slice(&2u32.to_le_bytes());
        table.extend_from_slice(&8u16.to_le_bytes());
        table.extend_from_slice(&(page.len() as u16).to_le_bytes());
        for &(code, frame) in page {
            ensure!(frame < 1 << 24, "unwind tables too large");
            table.extend_from_slice(&code.to_le_bytes());
            table.extend_from_slice(&(DWARF | frame).to_le_bytes());
        }
    }
    Ok(table)
}

/// How long `unwind_table` makes the table for this many frames.
fn unwind_table_len(old: &[u8], frames: usize) -> anyhow::Result<usize> {
    let (index, pages) = (u32_at(old, 24)? as usize, frames.div_ceil(500));
    Ok(old.len().next_multiple_of(4) + (index + pages) * 12 + pages * 8 + frames * 8)
}

/// The instructions a relocation is written into.
struct Code;

impl Code {
    /// How far a branch reaches.
    const REACH: i64 = 1 << 27;
    /// `adrp x16`, `add x16, x16` and `ldr x16, [x16]`, without what they add, and `br x16`.
    const PAGE_OF: u32 = 0x9000_0010;
    const ADD: u32 = 0x9100_0210;
    const LOAD: u32 = 0xf940_0210;
    const JUMP: u32 = 0xd61f_0200;
    /// A stub: one of each.
    const STUB: usize = 12;

    fn reaches(to: u64, from: u64) -> bool {
        (-Self::REACH..Self::REACH).contains(&(to.wrapping_sub(from) as i64))
    }

    /// `b` or `bl` with where it goes.
    fn branch(instruction: u32, to: u64, from: u64) -> anyhow::Result<u32> {
        ensure!(Self::reaches(to, from) && to.is_multiple_of(4), "a branch out of reach");
        Ok(instruction & 0xfc00_0000 | (to.wrapping_sub(from) >> 2) as u32 & 0x03ff_ffff)
    }

    /// `adrp` with the page of `to`.
    fn page(instruction: u32, to: u64, from: u64) -> anyhow::Result<u32> {
        let pages = (to >> 12) as i64 - (from >> 12) as i64;
        ensure!((-(1 << 20)..1 << 20).contains(&pages), "the program is too large");
        let pages = pages as u32;
        Ok(instruction & 0x9f00_001f | (pages & 3) << 29 | (pages >> 2 & 0x7_ffff) << 5)
    }

    /// An `add`, or a load or store, with where in its page `to` is.
    fn offset(instruction: u32, to: u64) -> anyhow::Result<u32> {
        let mut within = (to & 0xfff) as u32;
        if instruction & 0x3b00_0000 == 0x3900_0000 {
            // A load or store counts in what it moves, 16 bytes when the register is a vector.
            let vector = instruction & 0x0480_0000 == 0x0480_0000;
            let scale = if vector { 4 } else { instruction >> 30 };
            ensure!(within.is_multiple_of(1 << scale), "a load of what is not aligned");
            within >>= scale;
        }
        Ok(instruction & !(0xfff << 10) | within << 10)
    }

    /// The code that jumps to `to`, or to the address in the slot at `to`.
    fn stub(to: u64, from: u64, through_slot: bool) -> anyhow::Result<[u8; Self::STUB]> {
        let second = if through_slot { Self::LOAD } else { Self::ADD };
        let code = [Self::page(Self::PAGE_OF, to, from)?, Self::offset(second, to)?, Self::JUMP];
        let mut stub = [0; Self::STUB];
        for (bytes, instruction) in stub.as_chunks_mut().0.iter_mut().zip(code) {
            *bytes = instruction.to_le_bytes();
        }
        Ok(stub)
    }
}

/// A patch object, and what of the executable it needs.
pub(super) struct Patch<'a> {
    file: object::File<'a>,
    /// The sections that are loaded, by the segment they go to.
    sections: [Vec<SectionIndex>; 2],
    code: FxHashSet<SectionIndex>,
    /// Its `__eh_frame`, which goes behind the program's.
    frames: Option<SectionIndex>,
    relocations: FxHashMap<SectionIndex, Vec<Relocation>>,
    /// What each symbol a relocation refers to stands for.
    targets: FxHashMap<SymbolIndex, Target>,
    /// The symbols the code reaches through an address slot of ours, in the order of the
    /// slots.
    slots: Vec<SymbolIndex>,
    /// The symbols of the executable that the code branches to, in the order of their stubs.
    stubs: Vec<SymbolIndex>,
    /// The functions and statics it defines, with what the executable has under the name.
    replaced: Vec<Replaced<'a>>,
    /// The statics among them that go where the executable has them, by where the patch does.
    in_place: FxHashMap<SectionIndex, Vec<InPlace>>,
}

const TEXT: usize = 0;
const DATA: usize = 1;

#[derive(Clone, Copy)]
enum Target {
    /// At an offset in a section of the patch.
    Ours(SectionIndex, u64),
    /// At an address of the executable.
    Theirs(u64),
    Import(Import),
}

struct Relocation {
    at: u64,
    fixup: Fixup,
    symbol: SymbolIndex,
    addend: i64,
}

/// How a relocation of the patch gets its value.
#[derive(Clone, Copy, PartialEq)]
enum Fixup {
    /// The address itself, in 8 bytes.
    Absolute,
    /// How far the address is from that of another symbol, in this many bytes.
    Distance(SymbolIndex, usize),
    Branch,
    /// The page of the address, and where in the page it is.
    Page,
    Offset,
    /// The same of a slot that holds the address.
    SlotPage,
    SlotOffset,
    /// The distance to such a slot, in 4 bytes.
    SlotDistance,
}

impl Fixup {
    fn through_slot(self) -> bool {
        matches!(self, Fixup::SlotPage | Fixup::SlotOffset | Fixup::SlotDistance)
    }
}

pub(super) struct Replaced<'a> {
    pub(super) name: &'a [u8],
    section: SectionIndex,
    offset: u64,
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

impl<'a> Patch<'a> {
    const SLOT: usize = 8;

    fn read(bytes: &'a [u8], image: &Image) -> anyhow::Result<Patch<'a>> {
        let file = object::File::parse(bytes)?;
        let mut patch = Patch {
            file,
            sections: Default::default(),
            code: FxHashSet::default(),
            frames: None,
            relocations: FxHashMap::default(),
            targets: FxHashMap::default(),
            slots: Vec::new(),
            stubs: Vec::new(),
            replaced: Vec::new(),
            in_place: FxHashMap::default(),
        };
        for section in patch.file.sections() {
            let SectionFlags::MachO { flags } = section.flags() else {
                bail!("a patch that is not Mach-O")
            };
            let kind = flags & macho::SECTION_TYPE;
            ensure!(
                !(macho::S_THREAD_LOCAL_REGULAR..=macho::S_THREAD_LOCAL_INIT_FUNCTION_POINTERS)
                    .contains(&kind),
                "the patch has thread-local data"
            );
            if flags & macho::S_ATTR_DEBUG != 0 || section.size() == 0 {
                continue;
            }
            let relocations = Self::relocations(&section)?;
            let stores = relocations.iter().any(|it| it.fixup == Fixup::Absolute);
            let writable =
                section.segment_name_bytes()?.is_some_and(|it| it.starts_with(b"__DATA"));
            if section.name_bytes()? == b"__eh_frame" {
                ensure!(!stores && patch.frames.is_none(), "frames that store addresses");
                patch.frames = Some(section.index());
            } else if flags & (macho::S_ATTR_PURE_INSTRUCTIONS | macho::S_ATTR_SOME_INSTRUCTIONS)
                != 0
            {
                ensure!(!stores, "code that stores addresses");
                patch.code.insert(section.index());
                patch.sections[TEXT].push(section.index());
            } else if stores || writable || kind == macho::S_ZEROFILL {
                patch.sections[DATA].push(section.index());
            } else {
                patch.sections[TEXT].push(section.index());
            }
            patch.relocations.insert(section.index(), relocations);
        }

        // No symbol has a size: one reaches to the next of its section.
        let mut starts: Vec<u64> =
            patch.file.symbols().filter(|it| it.is_definition()).map(|it| it.address()).collect();
        starts.sort_unstable();
        starts.dedup();
        for symbol in patch.file.symbols() {
            if !symbol.is_definition() || symbol.is_local() {
                continue;
            }
            let name = symbol.name_bytes()?;
            let shown = || String::from_utf8_lossy(name);
            let index = symbol.section_index().context("a symbol in no section")?;
            let section = patch.file.section_by_index(index)?;
            ensure!(
                patch.relocations.contains_key(&index),
                "{} is in a section that is not loaded",
                shown()
            );
            let offset = symbol.address() - section.address();
            let code = patch.code.contains(&index);
            let old = match image.symbols.get(name) {
                None => None,
                Some(Named::One(old)) if old.kind == SymbolKind::Text && code => Some(*old),
                Some(Named::One(old)) if old.kind == SymbolKind::Data && !code => {
                    let next = starts.get(starts.partition_point(|it| *it <= symbol.address()));
                    let end = section.address() + section.size();
                    let size = next.map_or(end, |next| end.min(*next)) - symbol.address();
                    let new = InPlace { offset, size, old: *old };
                    patch
                        .fits(&new, &section, image)
                        .with_context(|| format!("the static {} has another value", shown()))?;
                    patch.in_place.entry(index).or_default().push(new);
                    Some(*old)
                }
                Some(_) => {
                    bail!("the patch replaces {}, which is not one function or static", shown())
                }
            };
            patch.replaced.push(Replaced { name, section: index, offset, old });
        }

        let (mut slots, mut stubs) = (FxHashSet::default(), FxHashSet::default());
        let mut targets = FxHashMap::default();
        for relocation in patch.relocations.values().flatten() {
            let symbols = match relocation.fixup {
                Fixup::Distance(from, _) => vec![relocation.symbol, from],
                _ => vec![relocation.symbol],
            };
            for symbol in symbols {
                if let std::collections::hash_map::Entry::Vacant(unseen) = targets.entry(symbol) {
                    unseen.insert(patch.target(symbol, image)?);
                }
            }
            let target = targets[&relocation.symbol];
            let shown = || {
                let symbol = patch.file.symbol_by_index(relocation.symbol);
                symbol.ok().and_then(|it| it.name().ok()).unwrap_or_default().to_owned()
            };
            match (relocation.fixup, target) {
                (
                    Fixup::Absolute | Fixup::Distance(..) | Fixup::Page | Fixup::Offset,
                    Target::Import(_),
                ) => {
                    bail!("the address of {}, which is in another library", shown())
                }
                (fixup, Target::Import(Import { slot: None, .. })) if fixup.through_slot() => {
                    bail!("{}, which the executable has no address slot of", shown())
                }
                (Fixup::Branch, Target::Import(Import { slot: None, stub: None })) => {
                    bail!("{}, which the executable does not call", shown())
                }
                (Fixup::Branch, Target::Theirs(_) | Target::Import(_)) => {
                    if stubs.insert(relocation.symbol) {
                        patch.stubs.push(relocation.symbol);
                    }
                }
                (fixup, Target::Ours(..) | Target::Theirs(_)) if fixup.through_slot() => {
                    if slots.insert(relocation.symbol) {
                        patch.slots.push(relocation.symbol);
                    }
                }
                _ => {}
            }
        }
        patch.targets = targets;
        Ok(patch)
    }

    /// The relocations of a section, with the two that make a distance as one.
    fn relocations(section: &object::Section<'_, '_>) -> anyhow::Result<Vec<Relocation>> {
        let mut found = Vec::new();
        let mut from = None;
        for (at, relocation) in section.relocations() {
            let RelocationFlags::MachO { r_type, r_pcrel, r_length } = relocation.flags() else {
                bail!("a relocation that is not Mach-O's")
            };
            let RelocationTarget::Symbol(symbol) = relocation.target() else {
                bail!("a relocation against a section")
            };
            let fixup = match (r_type, r_pcrel, r_length) {
                (macho::ARM64_RELOC_SUBTRACTOR, false, 2 | 3) => {
                    from = Some(symbol);
                    continue;
                }
                (macho::ARM64_RELOC_UNSIGNED, false, 2 | 3) if from.is_some() => {
                    Fixup::Distance(from.take().context("no symbol")?, 1 << r_length)
                }
                (macho::ARM64_RELOC_UNSIGNED, false, 3) => Fixup::Absolute,
                (macho::ARM64_RELOC_BRANCH26, true, 2) => Fixup::Branch,
                (macho::ARM64_RELOC_PAGE21, true, 2) => Fixup::Page,
                (macho::ARM64_RELOC_PAGEOFF12, false, 2) => Fixup::Offset,
                (macho::ARM64_RELOC_GOT_LOAD_PAGE21, true, 2) => Fixup::SlotPage,
                (macho::ARM64_RELOC_GOT_LOAD_PAGEOFF12, false, 2) => Fixup::SlotOffset,
                (macho::ARM64_RELOC_POINTER_TO_GOT, true, 2) => Fixup::SlotDistance,
                (
                    macho::ARM64_RELOC_TLVP_LOAD_PAGE21 | macho::ARM64_RELOC_TLVP_LOAD_PAGEOFF12,
                    ..,
                ) => {
                    bail!("code that uses a thread-local")
                }
                (other, ..) => bail!("a relocation of type {other}, which only the linker handles"),
            };
            found.push(Relocation { at, fixup, symbol, addend: relocation.addend() });
        }
        ensure!(from.is_none(), "half of a distance");
        Ok(found)
    }

    /// Whether a static can go where the executable has the one it replaces: what refers to
    /// it there is not looked for.
    fn fits(
        &self,
        new: &InPlace,
        section: &object::Section<'_, '_>,
        image: &Image,
    ) -> anyhow::Result<()> {
        let old = &new.old;
        ensure!(new.size <= old.size, "that is larger: {} bytes after {}", new.size, old.size);
        let align = (new.offset | section.align().max(1) | 1 << 12).isolate_lowest_one();
        ensure!(old.address.is_multiple_of(align), "that may be aligned to {align}");
        let segment = (image.segments.iter())
            .find(|it| {
                it.address <= old.address && old.address + new.size <= it.address + it.file_size
            })
            .context("that the file has no bytes for")?;
        let writable = section.segment_name_bytes()?.is_some_and(|it| it.starts_with(b"__DATA"));
        ensure!(!writable || segment.writable, "that is written to, where the old one is not");
        Ok(())
    }

    fn target(&self, index: SymbolIndex, image: &Image) -> anyhow::Result<Target> {
        let symbol = self.file.symbol_by_index(index)?;
        let name = symbol.name_bytes()?;
        let shown = || String::from_utf8_lossy(name);
        if let Some(section) = symbol.section_index() {
            ensure!(
                self.relocations.contains_key(&section),
                "{} is in a section that is not loaded",
                shown()
            );
            let start = self.file.section_by_index(section)?.address();
            return Ok(Target::Ours(section, symbol.address() - start));
        }
        ensure!(symbol.is_undefined(), "{} is neither defined nor undefined", shown());
        match image.symbols.get(name) {
            Some(Named::One(Defined { kind: SymbolKind::Tls, .. })) => {
                bail!("{} is thread-local", shown())
            }
            Some(Named::One(defined)) => Ok(Target::Theirs(defined.address)),
            Some(Named::Many) => bail!("{} names several things in the executable", shown()),
            None => match image.imports.get(name) {
                Some(import) => Ok(Target::Import(*import)),
                None => bail!("{} is not in the executable", shown()),
            },
        }
    }

    /// Lays the patch out where `__LINKEDIT` is and gives everything in it its address.
    fn place(&self, image: &Image) -> anyhow::Result<Addition> {
        let linkedit = image.linkedit();
        let (offset, base) = (linkedit.offset, linkedit.address);
        let old_frames = image.frames.bytes.len().next_multiple_of(8);
        let frames = match self.frames {
            Some(index) => {
                let section = self.file.section_by_index(index)?;
                Pointer::all(section.data()?)?.iter().filter(|it| it.frame.is_some()).count()
            }
            None => 0,
        };

        // Where everything goes, as offsets from `base`.
        let mut end = 0u64;
        let mut reserve = |len: usize, align: u64| {
            let start = end.next_multiple_of(align);
            end = start + len as u64;
            start
        };
        // And the tables of the unwinder, as offsets from where they may start.
        let (tables, tables_end) = image.tables;
        let mut placed = FxHashMap::default();
        let frames_at = unwind_table_len(&image.unwind.bytes, frames)?.next_multiple_of(8) as u64;
        let mut frames_end = frames_at + old_frames as u64;
        if let Some(index) = self.frames {
            placed.insert(index, frames_end);
            frames_end += self.file.section_by_index(index)?.size();
        }
        ensure!(
            tables + frames_end <= tables_end,
            "the tables of the unwinder have no room to grow in `__TEXT`"
        );
        let mut rewritten = vec![0u8; (tables_end - tables) as usize];
        let (mut stubs_at, mut code_end, mut data_at) = (0, 0, 0);
        for (segment, sections) in self.sections.iter().enumerate() {
            for &index in sections {
                let section = self.file.section_by_index(index)?;
                placed.insert(index, reserve(section.size() as usize, section.align().max(1)));
            }
            if segment == TEXT {
                stubs_at = reserve(self.stubs.len() * Code::STUB, 4);
                code_end = reserve(0, 1);
                data_at = reserve(0, PAGE);
            }
        }
        // A segment of nothing is not one.
        let slots_at = reserve(self.slots.len().max(1) * Self::SLOT, 8);
        let linkedit_at = reserve(0, PAGE);
        let mut appended = vec![0u8; linkedit_at as usize];

        // A static written in place is where the executable has it: its section is added
        // as a whole, with a copy of it that nothing may use.
        let address = |target: Target, added: i64| -> anyhow::Result<u64> {
            let (section, at) = match target {
                Target::Ours(section, at) => (section, at),
                Target::Theirs(address) => return Ok(address.wrapping_add_signed(added)),
                Target::Import(_) => bail!("the address of what is in another library"),
            };
            let in_place = self.in_place.get(&section).map_or(&[][..], |it| it);
            Ok(match in_place.iter().find(|it| it.holds(at)) {
                Some(it) => it.old.address + (at - it.offset),
                None if Some(section) == self.frames => tables + placed[&section] + at,
                None => base + placed[&section] + at,
            }
            .wrapping_add_signed(added))
        };
        let slot_of: FxHashMap<SymbolIndex, u64> = (self.slots.iter().copied())
            .zip((0..).map(|at| base + slots_at + at * Self::SLOT as u64))
            .collect();
        let stub_of: FxHashMap<SymbolIndex, u64> = (self.stubs.iter().copied())
            .zip((0..).map(|at| base + stubs_at + at * Code::STUB as u64))
            .collect();
        let slot = |relocation: &Relocation| match self.targets[&relocation.symbol] {
            Target::Import(Import { slot: Some(slot), .. }) => slot,
            _ => slot_of[&relocation.symbol],
        };

        let mut overwritten = Vec::new();
        // The addresses stored in data, which the loader moves with the program: those of
        // the patch, and those of the statics written in place, by where.
        let mut stored = Vec::new();
        let mut restored = FxHashSet::default();
        for section in self.file.sections() {
            let Some(&start) = placed.get(&section.index()) else { continue };
            let data = section.data()?;
            let (buffer, origin) = match self.frames == Some(section.index()) {
                true => (&mut rewritten, tables),
                false => (&mut appended, base),
            };
            buffer[start as usize..][..data.len()].copy_from_slice(data);
            let in_place = self.in_place.get(&section.index()).map_or(&[][..], |it| it);
            let mut values: Vec<Vec<u8>> = in_place
                .iter()
                .map(|it| match data.get(it.offset as usize..(it.offset + it.size) as usize) {
                    Some(value) => value.to_vec(),
                    None => vec![0; it.size as usize],
                })
                .collect();
            for relocation in &self.relocations[&section.index()] {
                let target = self.targets[&relocation.symbol];
                let at = (start + relocation.at) as usize;
                let place = origin + at as u64;
                let field =
                    |len: usize| buffer.get(at..at + len).context("a relocation past its section");
                if let Some(which) = in_place.iter().position(|it| it.holds(relocation.at)) {
                    ensure!(relocation.fixup == Fixup::Absolute, "a static that stores a distance");
                    let within = (relocation.at - in_place[which].offset) as usize;
                    let value = address(target, relocation.addend + u64_at(field(8)?, 0)? as i64)?;
                    let field = values[which].get_mut(within..within + 8);
                    field
                        .context("an address past its static")?
                        .copy_from_slice(&value.to_le_bytes());
                    restored.insert(in_place[which].old.address + within as u64);
                    continue;
                }
                match relocation.fixup {
                    Fixup::Absolute => {
                        let value =
                            address(target, relocation.addend + u64_at(field(8)?, 0)? as i64)?;
                        put64(buffer, at, value);
                        stored.push(place);
                    }
                    Fixup::Distance(from, len) => {
                        let from = address(self.targets[&from], 0)?;
                        let written = match len {
                            4 => i64::from(u32_at(field(4)?, 0)? as i32),
                            _ => u64_at(field(8)?, 0)? as i64,
                        };
                        let to = address(target, relocation.addend + written)?;
                        let distance = to.wrapping_sub(from).to_le_bytes();
                        buffer[at..at + len].copy_from_slice(&distance[..len]);
                    }
                    Fixup::SlotDistance => {
                        let written = i64::from(u32_at(field(4)?, 0)? as i32);
                        let to = slot(relocation).wrapping_add_signed(relocation.addend + written);
                        let distance = i32::try_from(to.wrapping_sub(place) as i64);
                        put32(buffer, at, distance.context("the program is too large")? as u32);
                    }
                    fixup => {
                        let instruction = u32_at(field(4)?, 0)?;
                        let instruction = match fixup {
                            Fixup::Branch => {
                                let direct = match target {
                                    Target::Import(Import { stub, .. }) => stub,
                                    _ => Some(address(target, relocation.addend)?),
                                };
                                let to = direct
                                    .filter(|to| Code::reaches(*to, place))
                                    .unwrap_or_else(|| stub_of[&relocation.symbol]);
                                Code::branch(instruction, to, place)?
                            }
                            Fixup::Page => {
                                Code::page(instruction, address(target, relocation.addend)?, place)?
                            }
                            Fixup::Offset => {
                                Code::offset(instruction, address(target, relocation.addend)?)?
                            }
                            Fixup::SlotPage => Code::page(instruction, slot(relocation), place)?,
                            _ => Code::offset(instruction, slot(relocation))?,
                        };
                        put32(buffer, at, instruction);
                    }
                }
            }
            for (new, value) in in_place.iter().zip(values) {
                overwritten.push((image.offset_of(new.old.address)?, value));
            }
        }
        for (&index, &slot) in &slot_of {
            put64(&mut appended, (slot - base) as usize, address(self.targets[&index], 0)?);
            stored.push(slot);
        }
        for (&index, &stub) in &stub_of {
            let code = match self.targets[&index] {
                Target::Import(Import { stub: Some(theirs), .. }) => {
                    Code::stub(theirs, stub, false)?
                }
                Target::Import(Import { slot: Some(slot), .. }) => Code::stub(slot, stub, true)?,
                target => Code::stub(address(target, 0)?, stub, false)?,
            };
            appended[(stub - base) as usize..][..Code::STUB].copy_from_slice(&code);
        }

        // The frames: the program's, which say how far their code is from where they were,
        // and the patch's behind them.
        let image_base = image.base()?;
        let frames_address = tables + frames_at;
        let moved = frames_address.wrapping_sub(image.frames.address) as i64;
        let section = &mut rewritten[frames_at as usize..frames_end as usize];
        section[..image.frames.bytes.len()].copy_from_slice(&image.frames.bytes);
        for pointer in Pointer::all(&image.frames.bytes)? {
            if pointer.relative {
                let value = pointer.value(section)?.wrapping_sub(moved);
                match pointer.len {
                    4 => put32(
                        section,
                        pointer.at,
                        i32::try_from(value).context("the program is too large")? as u32,
                    ),
                    _ => put64(section, pointer.at, value as u64),
                }
            }
        }
        let mut entries = Vec::with_capacity(frames);
        let ours = &section[old_frames..];
        for pointer in Pointer::all(ours)? {
            let Some(frame) = pointer.frame else { continue };
            ensure!(pointer.relative, "frames whose code is not relative to them");
            let at = frames_address + (old_frames + pointer.at) as u64;
            let code = at.wrapping_add_signed(pointer.value(ours)?);
            entries.push((u32::try_from(code - image_base)?, u32::try_from(old_frames + frame)?));
        }
        entries.sort_unstable();
        let unwind = unwind_table(
            &image.unwind.bytes,
            &entries,
            u32::try_from(base + code_end - image_base)?,
        )?;
        ensure!(unwind.len() <= frames_at as usize, "an unwind table longer than planned");
        rewritten[..unwind.len()].copy_from_slice(&unwind);
        overwritten.push((image.offset_of(tables)?, rewritten));

        // The symbols of the functions name the new code, for whoever reads a backtrace.
        let mut renamed = Vec::new();
        let mut redirected = 0;
        for replaced in &self.replaced {
            let Some(old) = replaced.old.filter(|it| it.kind == SymbolKind::Text) else { continue };
            let new = base + placed[&replaced.section] + replaced.offset;
            let shown = || String::from_utf8_lossy(replaced.name);
            let jump = if Code::reaches(new, old.address) {
                Code::branch(0x1400_0000, new, old.address)?.to_le_bytes().to_vec()
            } else {
                ensure!(
                    old.size >= Code::STUB as u64,
                    "{} is too short to jump so far from",
                    shown()
                );
                Code::stub(new, old.address, false)?.to_vec()
            };
            ensure!(old.size >= jump.len() as u64, "{} is too short to jump from", shown());
            overwritten.push((image.offset_of(old.address)?, jump));
            renamed.push((old.entry, new));
            redirected += 1;
        }

        let mut rebases: Vec<u64> = image.rebases.clone();
        let statics: Vec<Defined> = self.in_place.values().flatten().map(|it| it.old).collect();
        rebases
            .retain(|at| !statics.iter().any(|it| (it.address..it.address + it.size).contains(at)));
        rebases.extend(restored);
        rebases.extend(stored);
        rebases.sort_unstable();
        rebases.dedup();

        let text = (base, data_at);
        let data = (base + data_at, linkedit_at - data_at);
        let tables =
            [(tables, unwind.len()), (tables + frames_at, (frames_end - frames_at) as usize)];
        let layout = Layout { text, data, tables, rebases, renamed };
        let (commands, linkedit) = layout.linked(image, offset + linkedit_at)?;
        ensure!(
            commands.len() <= image.room,
            "the header has no room for two more segments: link with -Wl,-headerpad,{:#x}",
            (commands.len() - image.commands.len()).next_multiple_of(0x100)
        );
        overwritten.push((0, commands));
        appended.extend_from_slice(&linkedit);
        Ok(Addition { offset, appended, overwritten, redirected })
    }
}

/// Where the splice put what the load commands and `__LINKEDIT` have to say.
struct Layout {
    /// The address and length of each new segment.
    text: (u64, u64),
    data: (u64, u64),
    /// The address and length of `__unwind_info` and `__eh_frame`.
    tables: [(u64, usize); 2],
    rebases: Vec<u64>,
    /// The entries of the symbol table that get another address.
    renamed: Vec<(u64, u64)>,
}

impl Layout {
    /// The header and load commands, and `__LINKEDIT` up to its signature at `offset`.
    fn linked(&self, image: &Image, offset: u64) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let old = image.linkedit();
        let address = self.data.0 + self.data.1;
        let mut commands = image.commands.clone();

        for (table, (at, len)) in [&image.unwind, &image.frames].into_iter().zip(self.tables) {
            put64(&mut commands, table.header + 32, at);
            put64(&mut commands, table.header + 40, len as u64);
            put32(&mut commands, table.header + 48, u32::try_from(image.offset_of(at)?)?);
        }
        if let Some(room) = image.room_for_tables {
            put64(&mut commands, room + 40, 0);
        }

        let mut added = Vec::new();
        let segment = |name: &[u8], (address, len): (u64, u64), protection: u32| {
            let mut command = vec![0; SEGMENT];
            put32(&mut command, 0, macho::LC_SEGMENT_64);
            put32(&mut command, 4, SEGMENT as u32);
            command[8..8 + name.len()].copy_from_slice(name);
            for (at, field) in
                [address, len, address - old.address + old.offset, len].into_iter().enumerate()
            {
                put64(&mut command, 24 + at * 8, field);
            }
            put32(&mut command, 56, protection);
            put32(&mut command, 60, protection);
            command
        };
        let run = macho::VM_PROT_READ | macho::VM_PROT_EXECUTE;
        added.extend(segment(b"__RUSTD_TEXT", self.text, run));
        added.extend(segment(
            b"__RUSTD_DATA",
            self.data,
            macho::VM_PROT_READ | macho::VM_PROT_WRITE,
        ));

        // `__LINKEDIT`: the fixups are written again, and what is behind them moves by as
        // much as they grew.
        let fixups = image.at.fixups;
        let (rebases, len) =
            (u32_at(&commands, fixups + 8)? as u64, u32_at(&commands, fixups + 12)? as u64);
        let rebases = if len == 0 { old.offset } else { rebases };
        let starts: Vec<u64> =
            (image.segments[..image.segments.len() - 1].iter().map(|it| it.address))
                .chain([self.text.0, self.data.0])
                .collect();
        let stream = Rebases::written(&self.rebases, &starts)?;
        let within = (rebases - old.offset) as usize;
        let mut linkedit = image.linkedit[..within].to_vec();
        linkedit.extend_from_slice(&stream);
        linkedit.extend_from_slice(&image.linkedit[within + len as usize..]);
        let moved = |at: u64| match at {
            0 => 0,
            at if at < rebases + len => at - old.offset + offset,
            at => at - old.offset + offset + stream.len() as u64 - len,
        };
        for (entry, address) in &self.renamed {
            put64(&mut linkedit, (moved(*entry) - offset) as usize + 8, *address);
        }
        // The signature is looked for right behind the strings, which end the rest, at the
        // next multiple of sixteen: what filled up to the old one is not kept.
        let strings = moved(u64::from(u32_at(&commands, image.at.symbols + 16)?))
            + u64::from(u32_at(&commands, image.at.symbols + 20)?);
        let filled = linkedit.get((strings - offset) as usize..).context("strings past the end")?;
        ensure!(
            filled.len() < 16 && filled.iter().all(|&it| it == 0),
            "strings that are not the last of `__LINKEDIT`"
        );
        linkedit.truncate((strings - offset) as usize);
        linkedit.resize(linkedit.len().next_multiple_of(16), 0);
        let signed = offset + linkedit.len() as u64;
        let signature = image.signature.len(signed) as u64;

        let mut fields = vec![fixups + 16, fixups + 24, fixups + 32, fixups + 40];
        fields.extend([image.at.symbols + 8, image.at.symbols + 16]);
        fields.extend([32, 40, 48, 56, 64, 72].map(|at| image.at.indirect + at));
        fields.extend(image.at.data.iter().map(|at| at + 8));
        for field in fields {
            let at = moved(u64::from(u32_at(&commands, field)?));
            put32(&mut commands, field, u32::try_from(at)?);
        }
        put32(&mut commands, fixups + 8, u32::try_from(offset + within as u64)?);
        put32(&mut commands, fixups + 12, u32::try_from(stream.len())?);
        put32(&mut commands, image.at.signature + 8, u32::try_from(signed)?);
        put32(&mut commands, image.at.signature + 12, u32::try_from(signature)?);
        let len = signed + signature - offset;
        for (at, field) in
            [address, len.next_multiple_of(PAGE), offset, len].into_iter().enumerate()
        {
            put64(&mut commands, image.at.linkedit + 24 + at * 8, field);
        }
        let (count, size) = (u32_at(&commands, 16)?, u32_at(&commands, 20)?);
        put32(&mut commands, 16, count + 2);
        put32(&mut commands, 20, size + added.len() as u32);
        commands.splice(image.at.linkedit..image.at.linkedit, added);
        Ok((commands, linkedit))
    }
}

/// What a splice writes.
struct Addition {
    /// Where in the file `appended` goes: over `__LINKEDIT`.
    offset: u64,
    /// The new segments and `__LINKEDIT` up to its signature.
    appended: Vec<u8>,
    /// What changes of the file before that, by where it is.
    overwritten: Vec<(u64, Vec<u8>)>,
    redirected: usize,
}

/// Brings the executable at `path` from what the linker wrote to that with `patch` in place
/// of the functions it defines.
pub(super) fn splice(
    image: &Image,
    path: &Path,
    baked: &[Box<[u8]>],
    undo: &mut Vec<(u64, Vec<u8>)>,
    stamp: &mut Stamp,
    patch: &[u8],
) -> anyhow::Result<Spliced> {
    let patch = Patch::read(patch, image)?;
    let defined: FxHashSet<&[u8]> = patch.replaced.iter().map(|it| it.name).collect();
    ensure!(
        baked.iter().all(|it| defined.contains(&**it)),
        "a function the executable was linked with a patch of is as it first was"
    );
    let addition = patch.place(image)?;

    ensure!(Stamp::of(&File::open(path)?)? == *stamp, "the executable was written by someone else");
    let mut copy = path.as_os_str().to_owned();
    copy.push(".spliced");
    _ = std::fs::remove_file(&copy);
    std::fs::copy(path, &copy)?;
    let written = (|| -> anyhow::Result<Stamp> {
        let file = OpenOptions::new().read(true).write(true).open(&copy)?;
        for (offset, bytes) in undo.drain(..).rev() {
            super::write_all_at(&file, &bytes, offset)?;
        }
        file.set_len(addition.offset)?;
        for (offset, bytes) in &addition.overwritten {
            let mut old = vec![0; bytes.len()];
            super::read_exact_at(&file, &mut old, *offset)?;
            undo.push((*offset, old));
            super::write_all_at(&file, bytes, *offset)?;
        }
        let signature = image.signature.of(
            &file,
            addition.offset,
            &addition.overwritten,
            &addition.appended,
        )?;
        super::write_all_at(&file, &addition.appended, addition.offset)?;
        super::write_all_at(&file, &signature, addition.offset + addition.appended.len() as u64)?;
        std::fs::rename(&copy, path)?;
        Stamp::of(&file)
    })();
    if written.is_err() {
        _ = std::fs::remove_file(&copy);
    }
    *stamp = written?;
    Ok(Spliced { redirected: addition.redirected, appended: addition.appended.len() })
}
