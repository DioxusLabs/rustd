//! Values in place of the slots of the frame that are only ever written whole and read whole.
//!
//! A local of a body is given a slot when the function is built, whether or not anything takes
//! its address, and most of what a body computes goes through a temporary that is written
//! once and read once. After the function is built, a part of a slot that one store writes,
//! and that nothing but loads of the same type reads, is the stored value where the store
//! dominates the load: the load and then the store are removed.

use cranelift_codegen::{
    dominator_tree::DominatorTree,
    flowgraph::ControlFlowGraph,
    ir::{self, InstructionData, Opcode, StackSlot, Value},
};
use rustc_hash::{FxHashMap, FxHashSet};

/// The stores and the loads of one part of a slot.
#[derive(Default)]
struct Part {
    stores: Vec<ir::Inst>,
    loads: Vec<ir::Inst>,
}

/// Removes the loads of `func` that read what a single store wrote to a slot whose address
/// goes nowhere else, and the stores nothing reads after that. A slot of `kept` is left as
/// it is: something outside the function reads it.
pub(super) fn promote(func: &mut ir::Function, kept: impl Iterator<Item = StackSlot>) {
    let mut escaped: FxHashSet<StackSlot> = kept.collect();
    let mut slot_of: FxHashMap<Value, StackSlot> = FxHashMap::default();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            if let InstructionData::StackAddr { stack_slot, offset, .. } = func.dfg.insts[inst] {
                if i32::from(offset) == 0 {
                    slot_of.insert(func.dfg.first_result(inst), stack_slot);
                } else {
                    escaped.insert(stack_slot);
                }
            }
        }
    }
    if slot_of.is_empty() {
        return;
    }
    let slot =
        |func: &ir::Function, value: Value| slot_of.get(&func.dfg.resolve_aliases(value)).copied();
    let mut parts: FxHashMap<StackSlot, FxHashMap<(i32, ir::Type), Part>> = FxHashMap::default();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            match func.dfg.insts[inst] {
                InstructionData::Load { opcode: Opcode::Load, arg, offset, .. } => {
                    let Some(slot) = slot(func, arg) else { continue };
                    let ty = func.dfg.value_type(func.dfg.first_result(inst));
                    let part = parts.entry(slot).or_default();
                    part.entry((offset.into(), ty)).or_default().loads.push(inst);
                }
                InstructionData::Store {
                    opcode: Opcode::Store,
                    args: [stored, to],
                    offset,
                    ..
                } => {
                    if let Some(slot) = slot(func, stored) {
                        escaped.insert(slot);
                    }
                    let Some(slot) = slot(func, to) else { continue };
                    let ty = func.dfg.value_type(stored);
                    let part = parts.entry(slot).or_default();
                    part.entry((offset.into(), ty)).or_default().stores.push(inst);
                }
                _ => {
                    for value in func.dfg.inst_values(inst) {
                        if let Some(slot) = slot(func, value) {
                            escaped.insert(slot);
                        }
                    }
                }
            }
        }
    }
    let mut dominators = None;
    for (slot, parts) in parts {
        if escaped.contains(&slot) {
            continue;
        }
        let mut spans: Vec<_> =
            parts.keys().map(|&(at, ty)| (at, at + ty.bytes() as i32)).collect();
        spans.sort_unstable();
        if spans.windows(2).any(|it| it[0].1 > it[1].0) {
            continue;
        }
        for part in parts.into_values() {
            let [store] = *part.stores.as_slice() else { continue };
            let InstructionData::Store { args: [stored, _], .. } = func.dfg.insts[store] else {
                continue;
            };
            let dominators = dominators.get_or_insert_with(|| dominator_tree(func));
            let mut read = false;
            for load in part.loads {
                if !dominators.dominates(store, load, &func.layout) {
                    read = true;
                    continue;
                }
                let loaded = func.dfg.first_result(load);
                func.dfg.detach_inst_results(load);
                func.dfg.change_to_alias(loaded, stored);
                func.layout.remove_inst(load);
            }
            if !read {
                func.layout.remove_inst(store);
            }
        }
    }
}

/// Empties the slots whose address is taken and then used for nothing, which promotion and
/// the registers locals are kept in leave behind: Cranelift gives a frame every slot it is
/// told of, used or not. A slot of `kept` is left as it is.
pub(super) fn empty_unused(func: &mut ir::Function, kept: impl Iterator<Item = StackSlot>) {
    let mut used: FxHashSet<StackSlot> = kept.collect();
    let mut read: FxHashSet<Value> = FxHashSet::default();
    let mut addrs = Vec::new();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            if let InstructionData::StackAddr { stack_slot, .. } = func.dfg.insts[inst] {
                addrs.push((func.dfg.first_result(inst), stack_slot));
            }
            read.extend(func.dfg.inst_values(inst).map(|it| func.dfg.resolve_aliases(it)));
        }
    }
    used.extend(addrs.into_iter().filter(|(addr, _)| read.contains(addr)).map(|it| it.1));
    for (slot, data) in func.sized_stack_slots.iter_mut() {
        if !used.contains(&slot) {
            data.size = 0;
        }
    }
}

/// What dominates what in `func`. Cranelift times working it out, and `wasm32-unknown-unknown`
/// has no clock to read: there, the thread is given a profiler that does not look at one.
fn dominator_tree(func: &ir::Function) -> DominatorTree {
    #[cfg(all(target_family = "wasm", target_os = "unknown"))]
    {
        use cranelift_codegen::timing::{Pass, Profiler, set_thread_profiler};
        struct Untimed;
        impl Profiler for Untimed {
            fn start_pass(&self, _: Pass) -> Box<dyn std::any::Any> {
                Box::new(())
            }
        }
        thread_local!(static UNTIMED: () = drop(set_thread_profiler(Box::new(Untimed))));
        UNTIMED.with(|_| ());
    }
    DominatorTree::with_function(func, &ControlFlowGraph::with_function(func))
}
