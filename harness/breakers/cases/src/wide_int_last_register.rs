//! A 128-bit integer argument that finds one integer register left goes on the stack. LLVM
//! then hands that register to the next integer and Cranelift to none, so an LLVM-built
//! caller and a Cranelift-built callee read the later arguments from different places.

use std::hint::black_box;

#[inline(never)]
fn spread(a: u8, b: i128, c: u64, d: i128, e: u32, f: i128, g: i128) -> (i128, u8, i128) {
    (b.wrapping_add(d) ^ f, a.wrapping_add(c as u8).wrapping_add(e as u8), g.wrapping_sub(b))
}

#[inline(never)]
fn after_two(a: u64, b: u64, c: u64, d: u64, e: u64, f: i128, g: u64) -> (i128, u64) {
    (f.wrapping_add((a + b + c + d + e) as i128), g)
}

// A pair whose first half is the 128-bit integer, then one whose second half is.
#[inline(never)]
fn wide_first(a: u64, b: u64, c: u64, d: u64, e: u64, f: (i128, u8), g: u64) -> (i128, u64) {
    (f.0 ^ f.1 as i128, a + b + c + d + e + g)
}

#[inline(never)]
fn wide_second(a: u64, b: u64, c: u64, d: u64, f: Option<i128>, g: u64, h: u64) -> (i128, u64) {
    (f.unwrap_or(5), a + b + c + d + g * 3 + h * 7)
}

pub fn run() -> ((i128, u8, i128), (i128, u64), (i128, u64), (i128, u64)) {
    let (a, b) = (black_box(i128::MIN + 7), black_box(-159i128));
    (
        spread(black_box(1), a, black_box(2), b, black_box(3), a ^ b, !a),
        after_two(1, 2, 3, 4, 5, black_box(-1 << 100), black_box(9)),
        wide_first(1, 2, 3, 4, 5, black_box((-3 << 90, 7)), black_box(11)),
        wide_second(1, 2, 3, 4, black_box(Some(-9 << 80)), black_box(13), black_box(17)),
    )
}
