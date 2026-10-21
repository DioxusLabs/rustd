//! Unwind tables (`.eh_frame`) and landing pads (`.gcc_except_table`), without which a panic
//! cannot cross a function we compiled. Ported from rustc's Cranelift backend. Windows has
//! tables of its own, which are in [`seh`].

use cranelift_codegen::{
    Context, FinalizedMachExceptionHandler,
    gimli::{
        self, Encoding, Format, RunTimeEndian, SectionId,
        write::{
            Address, CallFrameInstruction, CieId, EhFrame, EndianVec, FrameDescriptionEntry,
            FrameTable, Result as WriteResult, Writer,
        },
    },
    ir::{AbiParam, Signature, types},
    isa::{TargetIsa, unwind::UnwindInfo},
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{
    ObjectProduct,
    object::{
        BinaryFormat, RelocationEncoding, RelocationFlags, RelocationKind, macho,
        write::{Relocation, StandardSection},
    },
};

mod gcc_except_table;
pub(super) mod seh;

use gcc_except_table::{
    Action, ActionKind, ActionTable, CallSite, CallSiteTable, GccExceptTable, TypeInfoTable,
};

/// Exception tag of a landing pad that runs destructors and resumes unwinding.
pub(super) const CLEANUP: u32 = 0;
/// Exception tag of a landing pad that stops the unwind, for `catch_unwind`.
pub(super) const CATCH: u32 = 1;

const DATA_SYMBOL: usize = 1 << 31;

fn address_for_func(func: FuncId) -> Address {
    Address::Symbol { symbol: func.as_u32() as usize, addend: 0 }
}

fn address_for_data(data: DataId) -> Address {
    Address::Symbol { symbol: data.as_u32() as usize | DATA_SYMBOL, addend: 0 }
}

/// The frame layout and the landing pads of one compiled function, which do not depend on
/// where the function ends up.
#[derive(Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize)]
pub(super) struct FunctionUnwind {
    frame: Frame,
    /// The function's `.gcc_except_table` entry. A function without one has no call that
    /// lands anywhere, and no personality to ask.
    landing_pads: Option<Vec<u8>>,
}

/// How to find the caller's frame at each place in a function, as the producer of its code
/// tells it.
#[derive(Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize)]
enum Frame {
    /// Cranelift's rules, which are of the prologue alone, and the rules at each return.
    Cranelift(cranelift_codegen::isa::unwind::systemv::UnwindInfo, Vec<(u32, FrameRule)>),
    Rows(FrameRows),
    Windows(seh::Frame),
}

/// The rules of a function's `.eh_frame` entry, each with the offset in the function it
/// holds from.
#[derive(Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize)]
pub(super) struct FrameRows {
    /// How many bytes of code the rules cover.
    pub(super) len: u32,
    pub(super) rows: Vec<(u32, FrameRule)>,
}

/// A DWARF call frame instruction. Registers are DWARF register numbers, offsets are bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize)]
pub(super) enum FrameRule {
    Cfa(u16, i32),
    CfaRegister(u16),
    CfaOffset(i32),
    Offset(u16, i32),
    Restore(u16),
    SameValue(u16),
    Undefined(u16),
    RememberState,
    RestoreState,
    ArgsSize(u32),
}

impl FrameRule {
    /// What holds where a function is entered, which the entry every function shares says.
    /// On x86-64 the frame is eight bytes above the stack pointer, and the return address
    /// is at its bottom. On AArch64 the frame is at the stack pointer, and the return
    /// address is in a register.
    #[cfg(feature = "llvm")]
    pub(super) fn on_entry(arch: super::Arch) -> &'static [FrameRule] {
        match arch {
            super::Arch::Aarch64 => &[FrameRule::Cfa(31, 0)],
            super::Arch::Wasm32 => &[],
            super::Arch::X86_64 => &[FrameRule::Cfa(7, 8), FrameRule::Offset(16, -8)],
        }
    }

    fn instruction(self) -> CallFrameInstruction {
        let register = gimli::Register;
        match self {
            FrameRule::Cfa(reg, offset) => CallFrameInstruction::Cfa(register(reg), offset),
            FrameRule::CfaRegister(reg) => CallFrameInstruction::CfaRegister(register(reg)),
            FrameRule::CfaOffset(offset) => CallFrameInstruction::CfaOffset(offset),
            FrameRule::Offset(reg, offset) => CallFrameInstruction::Offset(register(reg), offset),
            FrameRule::Restore(reg) => CallFrameInstruction::Restore(register(reg)),
            FrameRule::SameValue(reg) => CallFrameInstruction::SameValue(register(reg)),
            FrameRule::Undefined(reg) => CallFrameInstruction::Undefined(register(reg)),
            FrameRule::RememberState => CallFrameInstruction::RememberState,
            FrameRule::RestoreState => CallFrameInstruction::RestoreState,
            FrameRule::ArgsSize(size) => CallFrameInstruction::ArgsSize(size),
        }
    }
}

impl FunctionUnwind {
    pub(super) fn of(isa: &dyn TargetIsa, context: &Context) -> Result<Option<Self>, String> {
        let Some(code) = context.compiled_code() else { return Ok(None) };
        let info = match code.create_unwind_info(isa).map_err(|e| e.to_string())? {
            Some(UnwindInfo::SystemV(info)) => info,
            Some(UnwindInfo::WindowsX64(info)) => {
                let (frame, landing_pads) = seh::function(code, &info)?;
                return Ok(Some(FunctionUnwind { frame: Frame::Windows(frame), landing_pads }));
            }
            _ => return Ok(None),
        };

        let mut table = GccExceptTable {
            call_sites: CallSiteTable(vec![]),
            actions: ActionTable::new(),
            type_info: TypeInfoTable::new(gimli::DW_EH_PE_udata4),
        };
        let catch_type = table.type_info.add(Address::Constant(0));
        let catch_action =
            table.actions.add(Action { kind: ActionKind::Catch(catch_type), next_action: None });
        for call_site in code.buffer.call_sites() {
            let start = u64::from(call_site.ret_addr - 1);
            if call_site.exception_handlers.is_empty() {
                table.call_sites.0.push(CallSite {
                    start,
                    length: 1,
                    landing_pad: 0,
                    action_entry: None,
                });
            }
            for handler in call_site.exception_handlers {
                let &FinalizedMachExceptionHandler::Tag(tag, landing_pad) = handler else {
                    return Err("unexpected exception handler".to_owned());
                };
                table.call_sites.0.push(CallSite {
                    start,
                    length: 1,
                    landing_pad: u64::from(landing_pad),
                    action_entry: (tag.as_u32() == CATCH).then_some(catch_action),
                });
            }
        }
        let encoding = Encoding {
            format: Format::Dwarf32,
            version: 1,
            address_size: isa.frontend_config().pointer_bytes(),
        };
        let mut writer = WriterRelocate::new();
        table.write(&mut writer, encoding).map_err(|e| e.to_string())?;
        debug_assert!(writer.relocs.is_empty());
        Ok(Some(FunctionUnwind {
            frame: Frame::Cranelift(info, at_returns(isa, code.buffer.data())),
            landing_pads: Some(writer.writer.into_vec()),
        }))
    }

    /// The unwind information of code that came with its own.
    #[cfg(feature = "llvm")]
    pub(super) fn from_rows(rows: FrameRows, landing_pads: Option<Vec<u8>>) -> Self {
        FunctionUnwind { frame: Frame::Rows(rows), landing_pads }
    }

    /// The unwind information of code of Windows that came with its own: how long the code
    /// is, its `UNWIND_INFO` less the handler, and its calls that have a landing pad.
    #[cfg(feature = "llvm")]
    pub(super) fn from_unwind_info(len: u32, info: Vec<u8>, pads: seh::Pads) -> Self {
        let frame = Frame::Windows(seh::Frame { len, info });
        FunctionUnwind { frame, landing_pads: pads.finish() }
    }

    /// The function's `.eh_frame` entry, which a frame of Windows has none of.
    fn fde(&self, address: Address) -> Option<FrameDescriptionEntry> {
        Some(match &self.frame {
            Frame::Windows(_) => return None,
            Frame::Cranelift(info, returns) => {
                let mut fde = info.to_fde(address);
                for &(offset, rule) in returns {
                    fde.add_instruction(offset, rule.instruction());
                }
                fde
            }
            Frame::Rows(FrameRows { len, rows }) => {
                let mut fde = FrameDescriptionEntry::new(address, *len);
                for &(offset, rule) in rows {
                    fde.add_instruction(offset, rule.instruction());
                }
                fde
            }
        })
    }
}

/// The rules at each return of `code`: the epilogue has put the frame back as it was on
/// entry, where Cranelift's rules still find it from the frame pointer, which by then is the
/// caller's. A profiler that samples a return unwinds to whatever the caller's frame holds
/// there otherwise. Not on Mach-O, whose linker makes compact entries of rules of the
/// prologue alone, as Apple's compilers write them.
fn at_returns(isa: &dyn TargetIsa, code: &[u8]) -> Vec<(u32, FrameRule)> {
    if isa.triple().binary_format != target_lexicon::BinaryFormat::Elf {
        return Vec::new();
    }
    let (returns, entry, saved): (Vec<_>, _, &[u16]) = match isa.triple().architecture {
        // Every epilogue of a frame is `mov %rbp, %rsp; pop %rbp`, then `ret` or `ret imm16`.
        target_lexicon::Architecture::X86_64 => {
            let returns = code.windows(5).enumerate().filter_map(|(at, it)| match it {
                [0x48, 0x89, 0xec, 0x5d, 0xc3] => Some((at + 4, 1)),
                [0x48, 0x89, 0xec, 0x5d, 0xc2] => Some((at + 4, 3)),
                _ => None,
            });
            (returns.collect(), FrameRule::Cfa(7, 8), &[3, 6, 12, 13, 14, 15])
        }
        target_lexicon::Architecture::Aarch64(_) => {
            let ret = 0xd65f_03c0_u32.to_le_bytes();
            let words = code.as_chunks::<4>().0.iter().enumerate();
            let returns = words.filter(|(_, it)| **it == ret).map(|(at, _)| (at * 4, 4));
            let saved =
                &[19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 72, 73, 74, 75, 76, 77, 78, 79];
            (returns.collect(), FrameRule::Cfa(31, 0), saved)
        }
        _ => return Vec::new(),
    };
    let rows = returns.into_iter().flat_map(|(at, len)| {
        let restore = saved.iter().map(move |&reg| (at, FrameRule::Restore(reg)));
        let after = (at + len < code.len()).then_some((at + len, FrameRule::RestoreState));
        [(at, FrameRule::RememberState), (at, entry)].into_iter().chain(restore).chain(after)
    });
    rows.map(|(at, rule)| (at as u32, rule)).collect()
}

/// The function the unwinder asks about a frame with landing pads: the program's own of that
/// name when it defines one, the runtime's otherwise.
fn personality(module: &mut dyn Module) -> Result<FuncId, String> {
    const NAME: &str = "rust_eh_personality";
    if let Some(cranelift_module::FuncOrDataId::Func(own)) = module.declarations().get_name(NAME) {
        return Ok(own);
    }
    let pointer = module.target_config().pointer_type();
    let signature = Signature {
        params: vec![
            AbiParam::new(types::I32),
            AbiParam::new(types::I32),
            AbiParam::new(types::I64),
            AbiParam::new(pointer),
            AbiParam::new(pointer),
        ],
        returns: vec![AbiParam::new(types::I32)],
        call_conv: module.target_config().default_call_conv,
    };
    module.declare_function(NAME, Linkage::Import, &signature).map_err(|e| e.to_string())
}

pub(super) struct UnwindContext {
    frame_table: FrameTable,
    cies: Option<Cies>,
    /// The pointer to the personality the frames name, where they reach it through one.
    personality_ref: Option<DataId>,
    seh: seh::Tables,
}

/// The entries functions share: one that names the personality, for functions with landing
/// pads, and one that does not.
#[derive(Clone, Copy)]
struct Cies {
    with_landing_pads: CieId,
    plain: CieId,
}

impl UnwindContext {
    pub(super) fn new(module: &mut dyn Module) -> Result<Self, String> {
        let mut frame_table = FrameTable::default();
        let seh = seh::Tables::default();
        let dwarf = module.isa().triple().binary_format != target_lexicon::BinaryFormat::Coff;
        // Nothing unwinds on wasm: a panic aborts there.
        if super::Target::current().is_wasm() {
            return Ok(UnwindContext { frame_table, cies: None, personality_ref: None, seh });
        }
        let Some(mut cie) = module.isa().create_systemv_cie().filter(|_| dwarf) else {
            return Ok(UnwindContext { frame_table, cies: None, personality_ref: None, seh });
        };
        let pcrel = gimli::DwEhPe(gimli::DW_EH_PE_pcrel.0 | gimli::DW_EH_PE_sdata4.0);
        cie.fde_address_encoding = pcrel;
        let plain = frame_table.add_cie(cie.clone());
        cie.lsda_encoding = Some(pcrel);

        let macho = module.isa().triple().binary_format == target_lexicon::BinaryFormat::Macho;
        // The personality is reached through a pointer, as it can live in another DSO. The
        // linker of Mach-O makes that pointer, when asked for the one among its own.
        if macho {
            let personality = personality(module)?;
            cie.personality = Some((
                gimli::DwEhPe(
                    gimli::DW_EH_PE_indirect.0 | gimli::DW_EH_PE_pcrel.0 | gimli::DW_EH_PE_sdata4.0,
                ),
                address_for_func(personality),
            ));
            let with_landing_pads = frame_table.add_cie(cie);
            return Ok(UnwindContext {
                cies: Some(Cies { with_landing_pads, plain }),
                personality_ref: None,
                frame_table,
                seh,
            });
        }
        // It must not be zero-initialized: the unwinder cannot handle it being in `.bss`.
        let personality_ref = module
            .declare_data("DW.ref.rust_eh_personality", Linkage::Local, false, false)
            .map_err(|e| e.to_string())?;
        // A linker of AArch64 may put more than four gigabytes between the two.
        let distance = match module.isa().triple().architecture {
            target_lexicon::Architecture::Aarch64(_) => gimli::DW_EH_PE_sdata8,
            _ => gimli::DW_EH_PE_sdata4,
        };
        cie.personality = Some((
            gimli::DwEhPe(gimli::DW_EH_PE_indirect.0 | gimli::DW_EH_PE_pcrel.0 | distance.0),
            address_for_data(personality_ref),
        ));

        let with_landing_pads = frame_table.add_cie(cie);
        Ok(UnwindContext {
            cies: Some(Cies { with_landing_pads, plain }),
            personality_ref: Some(personality_ref),
            frame_table,
            seh,
        })
    }

    /// Points the frames at the personality. Done once every function of the program is
    /// declared: a program without `std` may define the personality itself.
    pub(super) fn name_personality(&self, module: &mut dyn Module) -> Result<(), String> {
        let Some(personality_ref) = self.personality_ref else { return Ok(()) };
        let personality = personality(module)?;
        let mut data = DataDescription::new();
        data.define(
            vec![0; usize::from(module.target_config().pointer_bytes())].into_boxed_slice(),
        );
        let func_ref = module.declare_func_in_data(personality, &mut data);
        data.write_function_addr(0, func_ref);
        module.define_data(personality_ref, &data).map_err(|e| e.to_string())
    }

    /// The function `symbol` names, when it is one this object has for its own unwinding
    /// rather than one the build has.
    pub(super) fn runtime(
        &mut self,
        module: &mut dyn Module,
        symbol: &str,
    ) -> Result<Option<FuncId>, String> {
        self.seh.runtime(module, symbol)
    }

    /// Records the frame layout and the landing pads of a compiled function.
    pub(super) fn add_function(
        &mut self,
        module: &mut dyn Module,
        func: FuncId,
        unwind: &FunctionUnwind,
    ) -> Result<(), String> {
        if let Frame::Windows(frame) = &unwind.frame {
            return self.seh.add_function(module, func, frame, unwind.landing_pads.as_ref());
        }
        let Some(cies) = self.cies else { return Ok(()) };
        let Some(mut fde) = unwind.fde(address_for_func(func)) else { return Ok(()) };
        let Some(landing_pads) = &unwind.landing_pads else {
            self.frame_table.add_fde(cies.plain, fde);
            return Ok(());
        };
        let lsda = module.declare_anonymous_data(false, false).map_err(|e| e.to_string())?;
        let mut data = DataDescription::new();
        data.define(landing_pads.clone().into_boxed_slice());
        // Mach-O has room for 255 sections and every custom one counts, so there the tables
        // lie with the constants, where the unwinder finds them as well.
        if module.isa().triple().binary_format != target_lexicon::BinaryFormat::Macho {
            data.set_custom_section(".gcc_except_table");
        }
        module.define_data(lsda, &data).map_err(|e| e.to_string())?;
        fde.lsda = Some(address_for_data(lsda));

        self.frame_table.add_fde(cies.with_landing_pads, fde);
        Ok(())
    }

    pub(super) fn emit(self, product: &mut ObjectProduct) -> Result<(), String> {
        self.seh.emit(product)?;
        let mut eh_frame = EhFrame::from(WriterRelocate::new());
        self.frame_table.write_eh_frame(&mut eh_frame).map_err(|e| e.to_string())?;
        if eh_frame.0.writer.slice().is_empty() {
            return Ok(());
        }
        let section = product.object.section_id(StandardSection::EhFrame);
        product.object.section_mut(section).set_data(eh_frame.0.writer.into_vec(), 8);
        for reloc in &eh_frame.0.relocs {
            let symbol = if reloc.symbol & DATA_SYMBOL == 0 {
                product.function_symbol(FuncId::from_u32(reloc.symbol as u32))
            } else {
                product.data_symbol(DataId::from_u32((reloc.symbol & !DATA_SYMBOL) as u32))
            };
            // Local symbols are addressed through their section, except in Mach-O, whose
            // linker cuts a section into pieces at its symbols.
            let macho = product.object.format() == BinaryFormat::MachO;
            let (symbol, offset) = match macho {
                true => (symbol, 0),
                false => product.object.symbol_section_and_offset(symbol).unwrap_or((symbol, 0)),
            };
            let flags = match reloc.indirect && macho {
                true => RelocationFlags::MachO {
                    r_type: macho::ARM64_RELOC_POINTER_TO_GOT,
                    r_pcrel: true,
                    r_length: 2,
                },
                false => RelocationFlags::Generic {
                    kind: reloc.kind,
                    encoding: RelocationEncoding::Generic,
                    size: reloc.size * 8,
                },
            };
            product
                .object
                .add_relocation(
                    section,
                    Relocation {
                        offset: u64::from(reloc.offset),
                        symbol,
                        flags,
                        addend: offset as i64 + reloc.addend,
                    },
                )
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }
}

struct Reloc {
    offset: u32,
    size: u8,
    symbol: usize,
    addend: i64,
    kind: RelocationKind,
    /// Whether what is wanted is the address of a pointer to the symbol.
    indirect: bool,
}

/// A [`Writer`] that collects the relocations its output needs.
struct WriterRelocate {
    relocs: Vec<Reloc>,
    writer: EndianVec<RunTimeEndian>,
}

impl WriterRelocate {
    fn new() -> Self {
        WriterRelocate { relocs: Vec::new(), writer: EndianVec::new(RunTimeEndian::Little) }
    }
}

impl Writer for WriterRelocate {
    type Endian = RunTimeEndian;

    fn endian(&self) -> Self::Endian {
        self.writer.endian()
    }

    fn len(&self) -> usize {
        self.writer.len()
    }

    fn write(&mut self, bytes: &[u8]) -> WriteResult<()> {
        self.writer.write(bytes)
    }

    fn write_at(&mut self, offset: usize, bytes: &[u8]) -> WriteResult<()> {
        self.writer.write_at(offset, bytes)
    }

    fn write_address(&mut self, address: Address, size: u8) -> WriteResult<()> {
        match address {
            Address::Constant(val) => self.write_udata(val, size),
            Address::Symbol { symbol, addend } => {
                self.relocs.push(Reloc {
                    offset: self.len() as u32,
                    size,
                    symbol,
                    addend,
                    kind: RelocationKind::Absolute,
                    indirect: false,
                });
                self.write_udata(0, size)
            }
        }
    }

    // `.eh_frame` and the exception table never refer to other debug sections.
    fn write_offset(&mut self, _val: usize, _section: SectionId, _size: u8) -> WriteResult<()> {
        Err(gimli::write::Error::InvalidAttributeValue)
    }

    fn write_offset_at(
        &mut self,
        _offset: usize,
        val: usize,
        section: SectionId,
        size: u8,
    ) -> WriteResult<()> {
        self.write_offset(val, section, size)
    }

    fn write_eh_pointer(
        &mut self,
        address: Address,
        eh_pe: gimli::DwEhPe,
        size: u8,
    ) -> WriteResult<()> {
        match address {
            Address::Constant(val) => {
                let val = match eh_pe.application() {
                    gimli::DW_EH_PE_absptr => val,
                    gimli::DW_EH_PE_pcrel => (self.len() as u64).wrapping_sub(val),
                    _ => return Err(gimli::write::Error::UnsupportedPointerEncoding(eh_pe)),
                };
                self.write_eh_pointer_data(val, eh_pe.format(), size)
            }
            Address::Symbol { symbol, addend } => {
                let (kind, size) = match (eh_pe.application(), eh_pe.format()) {
                    (gimli::DW_EH_PE_pcrel, gimli::DW_EH_PE_sdata4) => {
                        (RelocationKind::Relative, 4)
                    }
                    (gimli::DW_EH_PE_pcrel, gimli::DW_EH_PE_sdata8) => {
                        (RelocationKind::Relative, 8)
                    }
                    (gimli::DW_EH_PE_absptr, _) => (RelocationKind::Absolute, size),
                    _ => return Err(gimli::write::Error::UnsupportedPointerEncoding(eh_pe)),
                };
                self.relocs.push(Reloc {
                    offset: self.len() as u32,
                    size,
                    symbol,
                    addend,
                    kind,
                    indirect: eh_pe.is_indirect(),
                });
                self.write_udata(0, size)
            }
        }
    }
}
