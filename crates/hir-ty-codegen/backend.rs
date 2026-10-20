//! Which code producer turns the IR of a function into machine code, and what each one did.
//!
//! A producer takes the Cranelift IR the front half builds from MIR, after layout and the
//! calling convention have been decided, and gives back a [`Code`]: bytes, the relocations
//! in them, and how to unwind through them. Nothing after that can tell the producers apart.
//! LLVM hands a function it has no lowering for to Cranelift, and says why.

use std::{
    collections::BTreeMap,
    fmt,
    sync::{
        Mutex, OnceLock,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
    time::Duration,
};

use stdx::time::Instant;

use super::{CodegenError, Result, debuginfo::SlotPlaces, fragment::Code, fragment::Recorder};

/// Names the producer: `cranelift` (the default) or `llvm`.
const BACKEND: &str = "RUSTD_BACKEND";
/// How hard LLVM optimizes each function, `0` to `3`. Functions are compiled alone at any
/// level: nothing is inlined across them.
const OPTIMIZATION: &str = "RUSTD_OPT";
/// How LLVM turns the optimized function into machine code: `optimized` (the default) or
/// `fast`, its quick instruction selection and register allocation. Most of LLVM's time on a
/// function is here, not in the passes before it.
const SELECTION: &str = "RUSTD_EMIT";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Backend {
    Cranelift,
    Llvm(Optimization),
}

/// What LLVM does to a function: the passes over its IR, and how code is selected for what
/// they leave.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Optimization {
    pub passes: Passes,
    pub selection: Selection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Passes {
    None,
    Less,
    Default,
    Aggressive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Selection {
    Fast,
    Optimized,
}

impl Optimization {
    /// No passes and the quick selection: what a function too large for more is given.
    pub const NONE: Optimization =
        Optimization { passes: Passes::None, selection: Selection::Fast };
}

impl Backend {
    /// The producer the environment asks for, or what is wrong with what it asks.
    pub fn from_env() -> std::result::Result<Backend, String> {
        static SELECTED: OnceLock<std::result::Result<Backend, String>> = OnceLock::new();
        SELECTED.get_or_init(Self::read_env).clone()
    }

    fn read_env() -> std::result::Result<Backend, String> {
        let passes = match std::env::var(OPTIMIZATION).as_deref() {
            Ok("0") => Passes::None,
            Ok("1") => Passes::Less,
            Ok("2") | Err(_) => Passes::Default,
            Ok("3") => Passes::Aggressive,
            Ok(other) => return Err(format!("{OPTIMIZATION}={other}: expected 0, 1, 2 or 3")),
        };
        let selection = match std::env::var(SELECTION).as_deref() {
            Ok("fast") => Selection::Fast,
            Ok("optimized") | Err(_) if passes != Passes::None => Selection::Optimized,
            Ok("optimized") | Err(_) => Selection::Fast,
            Ok(other) => {
                return Err(format!("{SELECTION}={other}: expected `fast` or `optimized`"));
            }
        };
        let optimization = Optimization { passes, selection };
        match std::env::var(BACKEND).as_deref() {
            Ok("cranelift") | Err(_) => Ok(Backend::Cranelift),
            Ok("llvm") if cfg!(feature = "llvm") => Ok(Backend::Llvm(optimization)),
            Ok("llvm") => Err(format!("{BACKEND}=llvm: rustd was built without `--features llvm`")),
            Ok(other) => Err(format!("{BACKEND}={other}: expected `cranelift` or `llvm`")),
        }
    }

    /// Compiles the function `context` holds. `recorder` is where a producer asks for a
    /// function its own code calls that the IR did not name.
    pub(super) fn emit(
        recorder: &mut Recorder<'_>,
        context: &mut cranelift_codegen::Context,
    ) -> Result<Code> {
        let mut code = Self::produce(recorder, context)?;
        // A function is replaced in a linked program by a jump written over its entry, so
        // none is shorter than that jump. Nothing runs the bytes that make up the length.
        let target = super::Target::selected().map_err(CodegenError::Backend)?;
        if let Some((shortest, filler)) = target.arch.shortest_function()
            && code.bytes.len() < shortest
        {
            code.bytes.resize(shortest, filler);
        }
        Ok(code)
    }

    fn produce(
        recorder: &mut Recorder<'_>,
        context: &mut cranelift_codegen::Context,
    ) -> Result<Code> {
        match Self::from_env().map_err(CodegenError::Backend)? {
            Backend::Cranelift => Self::emit_with_cranelift(recorder, context),
            #[cfg(feature = "llvm")]
            Backend::Llvm(optimization) => Self::emit_with_llvm(recorder, context, optimization),
            #[cfg(not(feature = "llvm"))]
            Backend::Llvm(_) => Self::emit_with_cranelift(recorder, context),
        }
    }

    fn emit_with_cranelift(
        recorder: &mut Recorder<'_>,
        context: &mut cranelift_codegen::Context,
    ) -> Result<Code> {
        let start = Instant::now();
        let pairs = super::float_pair::lower(recorder, &mut context.func);
        let mut code = super::emit(context)?;
        if let Some(frame) = context.compiled_code().and_then(|it| it.buffer.frame_layout()) {
            code.slots = SlotPlaces::of_frame(recorder.isa, frame, recorder.named_slots());
        }
        if let Some(pairs) = pairs {
            pairs.hold(context, &mut code)?;
        }
        Tally::global().cranelift.add(start.elapsed(), code.bytes.len());
        Ok(code)
    }
}

#[cfg(feature = "llvm")]
impl Backend {
    /// What LLVM makes of the function, from the store if the same IR was compiled at the
    /// same level before. A function LLVM does not handle is Cranelift's, which the IR alone
    /// decides, so its code is kept under the same key.
    fn emit_with_llvm(
        recorder: &mut Recorder<'_>,
        context: &mut cranelift_codegen::Context,
        optimization: Optimization,
    ) -> Result<Code> {
        use super::{cached::StoredCode, store::Store};
        let key = StoredCode::key(
            optimization,
            &context.func,
            recorder.named_slots(),
            recorder.constants(),
        );
        let store = Store::global().zip(key);
        if let Some((store, key)) = store
            && let Some(stored) = store.lookup(&key).and_then(|it| StoredCode::decode(&it))
            && let Some(code) = stored.restore(recorder)
        {
            return Ok(code);
        }
        let mark = recorder.mark();
        let start = Instant::now();
        let code = match super::llvm::emit(recorder, &context.func, optimization) {
            Ok(code) => {
                Tally::global().llvm.add(start.elapsed(), code.bytes.len());
                code
            }
            Err(unhandled) => {
                Tally::global().fell_back(start.elapsed(), &unhandled.to_string());
                Self::emit_with_cranelift(recorder, context)?
            }
        };
        if let Some((store, key)) = store
            && let Some(stored) = StoredCode::of(&code, recorder, mark).and_then(|it| it.encode())
        {
            store.insert(&key, &stored);
        }
        Ok(code)
    }
}

impl fmt::Display for Backend {
    /// Also what tells the entries of one producer from another's in the store.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Backend::Cranelift => f.write_str("cranelift"),
            Backend::Llvm(Optimization { passes, selection }) => {
                let level = match passes {
                    Passes::None => 0,
                    Passes::Less => 1,
                    Passes::Default => 2,
                    Passes::Aggressive => 3,
                };
                write!(f, "llvm -O{level}")?;
                match selection {
                    Selection::Fast if *passes != Passes::None => f.write_str(" fast emit"),
                    _ => Ok(()),
                }
            }
        }
    }
}

/// What the producers did since the last report.
#[derive(Default)]
pub(super) struct Tally {
    cranelift: Produced,
    llvm: Produced,
    /// Time LLVM spent on functions it then gave up on.
    wasted: AtomicU64,
    /// Why LLVM left a function to Cranelift, and how often.
    fallbacks: Mutex<BTreeMap<String, usize>>,
    /// Functions too large for LLVM to optimize in reasonable time, compiled at `-O0`.
    pub(super) large: AtomicUsize,
    /// Where LLVM's time went.
    pub(super) phases: [AtomicU64; Phase::COUNT],
    /// Where the time around the producer went.
    steps: [AtomicU64; Step::COUNT],
}

#[derive(Default)]
struct Produced {
    functions: AtomicUsize,
    nanos: AtomicU64,
    bytes: AtomicUsize,
}

/// The steps of compiling one function with LLVM.
#[derive(Debug, Clone, Copy)]
pub(super) enum Phase {
    Lower,
    Verify,
    Optimize,
    Emit,
    Read,
}

impl Phase {
    const COUNT: usize = 5;
    const ALL: [Phase; Phase::COUNT] =
        [Phase::Lower, Phase::Verify, Phase::Optimize, Phase::Emit, Phase::Read];
}

/// The steps of compiling one function that are not the producer's.
#[derive(Debug, Clone, Copy)]
pub(super) enum Step {
    /// The types of a body.
    Infer,
    /// The MIR of a body, without the time its types took when they were asked for first.
    Mir,
    /// A generic body with the types of one instance in it.
    Monomorphize,
    /// From MIR to the IR the producer takes.
    Translate,
    /// Lines and variables for a debugger.
    Describe,
    /// Reading an entry of the store.
    StoreRead,
    /// Encoding an entry and adding it to the store.
    StoreWrite,
}

impl Step {
    const COUNT: usize = 7;
    const ALL: [(Step, &str); Step::COUNT] = [
        (Step::Infer, "infer"),
        (Step::Mir, "mir"),
        (Step::Monomorphize, "monomorphize"),
        (Step::Translate, "translate"),
        (Step::Describe, "describe"),
        (Step::StoreRead, "store read"),
        (Step::StoreWrite, "store write"),
    ];
}

impl Produced {
    fn add(&self, took: Duration, bytes: usize) {
        self.functions.fetch_add(1, Ordering::Relaxed);
        self.nanos.fetch_add(took.as_nanos() as u64, Ordering::Relaxed);
        self.bytes.fetch_add(bytes, Ordering::Relaxed);
    }

    fn take(&self) -> Option<String> {
        let functions = self.functions.swap(0, Ordering::Relaxed);
        let took = Duration::from_nanos(self.nanos.swap(0, Ordering::Relaxed));
        let bytes = self.bytes.swap(0, Ordering::Relaxed);
        (functions != 0).then(|| {
            let each = took / functions as u32;
            format!("{functions} functions, {bytes} bytes, {took:.1?} ({each:.1?} each)")
        })
    }
}

impl Tally {
    pub(super) fn global() -> &'static Tally {
        static TALLY: OnceLock<Tally> = OnceLock::new();
        TALLY.get_or_init(Tally::default)
    }

    #[cfg(feature = "llvm")]
    fn fell_back(&self, took: Duration, reason: &str) {
        self.wasted.fetch_add(took.as_nanos() as u64, Ordering::Relaxed);
        let mut fallbacks = self.fallbacks.lock().unwrap_or_else(|e| e.into_inner());
        *fallbacks.entry(reason.to_owned()).or_default() += 1;
    }

    #[cfg(feature = "llvm")]
    pub(super) fn time<T>(&self, phase: Phase, work: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let out = work();
        self.phases[phase as usize].fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        out
    }

    /// Runs `work` as part of `step`.
    pub(super) fn step<T>(&self, step: Step, work: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let out = work();
        self.add(step, start.elapsed());
        out
    }

    pub(super) fn add(&self, step: Step, took: Duration) {
        self.steps[step as usize].fetch_add(took.as_nanos() as u64, Ordering::Relaxed);
    }

    /// Says what was compiled by which producer since the last call, on stderr. Times are
    /// summed over the threads that compiled.
    pub(super) fn report(&self) {
        let fallbacks =
            std::mem::take(&mut *self.fallbacks.lock().unwrap_or_else(|e| e.into_inner()));
        let wasted = Duration::from_nanos(self.wasted.swap(0, Ordering::Relaxed));
        let phases = Phase::ALL.map(|phase| {
            Duration::from_nanos(self.phases[phase as usize].swap(0, Ordering::Relaxed))
        });
        let (llvm, cranelift) = (self.llvm.take(), self.cranelift.take());
        let large = self.large.swap(0, Ordering::Relaxed);
        let steps = Step::ALL.map(|(step, name)| {
            let took = Duration::from_nanos(self.steps[step as usize].swap(0, Ordering::Relaxed));
            format!("{name} {took:.1?}")
        });
        let selected = Self::selected_llvm();
        let stats = std::env::var_os("RUSTD_STATS").is_some();
        if !selected && !stats {
            return;
        }
        if stats {
            eprintln!("steps: {}", steps.join(", "));
        }
        if let Some(llvm) = llvm {
            let phases = std::iter::zip(Phase::ALL, phases)
                .map(|(phase, took)| format!("{} {took:.1?}", format!("{phase:?}").to_lowercase()))
                .collect::<Vec<_>>()
                .join(", ");
            eprintln!("backend: llvm compiled {llvm}: {phases}");
        }
        if large != 0 {
            eprintln!("backend: llvm compiled {large} large functions without optimization");
        }
        if let Some(cranelift) = cranelift {
            eprintln!("backend: cranelift compiled {cranelift}");
        }
        if !fallbacks.is_empty() {
            let count: usize = fallbacks.values().sum();
            eprintln!("backend: llvm left {count} functions to cranelift after {wasted:.1?}:");
            for (reason, count) in fallbacks {
                eprintln!("  {count}\t{reason}");
            }
        }
    }

    fn selected_llvm() -> bool {
        matches!(Backend::from_env(), Ok(Backend::Llvm(_)))
    }
}
