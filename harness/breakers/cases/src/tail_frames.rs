//! LLVM turned a call in tail position into a jump, so `hop_1` and `hop_2` left no frame, and
//! a backtrace from `hop_3` had one of the three where rustc's unoptimized build has all of
//! them (backtrace's `smoke_test_frames`).

use std::backtrace::Backtrace;

#[inline(never)]
fn hop_1(depth: usize) -> usize {
    hop_2(depth + 1)
}

#[inline(never)]
fn hop_2(depth: usize) -> usize {
    hop_3(depth + 1)
}

#[inline(never)]
fn hop_3(depth: usize) -> usize {
    let trace = Backtrace::force_capture().to_string();
    depth * 10 + trace.lines().filter(|it| it.contains("tail_frames::hop_")).count()
}

pub fn run() -> usize {
    hop_1(0)
}
