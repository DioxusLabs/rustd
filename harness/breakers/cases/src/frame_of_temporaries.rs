//! jsonschema compiles a chain of a thousand `$ref`s by recursing through a few functions on a
//! thread of 256k. Most of what a body computes goes through a temporary written once and read
//! once, which rustd keeps in a register and not in its slot; the slots were still in the frame,
//! and a frame of rustd's was nearly twice rustc's. A slot nothing reads is not in the frame.

use std::hint::black_box;

#[inline(never)]
fn level(depth: u32, above: usize, frame: &mut usize, words: &[u64]) -> u64 {
    let here = black_box(&above as *const usize as usize);
    *frame = above.wrapping_sub(here);
    let mut sum = depth as u64;
    sum = sum.wrapping_mul(31) ^ words.get(0).map(|it| it.rotate_left(0)).unwrap_or(0);
    sum = sum.wrapping_mul(31) ^ words.get(1).map(|it| it.rotate_left(1)).unwrap_or(1);
    sum = sum.wrapping_mul(31) ^ words.get(2).map(|it| it.rotate_left(2)).unwrap_or(2);
    sum = sum.wrapping_mul(31) ^ words.get(3).map(|it| it.rotate_left(3)).unwrap_or(3);
    sum = sum.wrapping_mul(31) ^ words.get(4).map(|it| it.rotate_left(4)).unwrap_or(4);
    sum = sum.wrapping_mul(31) ^ words.get(5).map(|it| it.rotate_left(5)).unwrap_or(5);
    sum = sum.wrapping_mul(31) ^ words.get(6).map(|it| it.rotate_left(6)).unwrap_or(6);
    sum = sum.wrapping_mul(31) ^ words.get(7).map(|it| it.rotate_left(7)).unwrap_or(7);
    sum = sum.wrapping_mul(31) ^ words.get(8).map(|it| it.rotate_left(8)).unwrap_or(8);
    sum = sum.wrapping_mul(31) ^ words.get(9).map(|it| it.rotate_left(9)).unwrap_or(9);
    sum = sum.wrapping_mul(31) ^ words.get(10).map(|it| it.rotate_left(10)).unwrap_or(10);
    sum = sum.wrapping_mul(31) ^ words.get(11).map(|it| it.rotate_left(11)).unwrap_or(11);
    sum = sum.wrapping_mul(31) ^ words.get(12).map(|it| it.rotate_left(12)).unwrap_or(12);
    sum = sum.wrapping_mul(31) ^ words.get(13).map(|it| it.rotate_left(13)).unwrap_or(13);
    sum = sum.wrapping_mul(31) ^ words.get(14).map(|it| it.rotate_left(14)).unwrap_or(14);
    sum = sum.wrapping_mul(31) ^ words.get(15).map(|it| it.rotate_left(15)).unwrap_or(15);
    sum = sum.wrapping_mul(31) ^ words.get(16).map(|it| it.rotate_left(16)).unwrap_or(16);
    sum = sum.wrapping_mul(31) ^ words.get(17).map(|it| it.rotate_left(17)).unwrap_or(17);
    sum = sum.wrapping_mul(31) ^ words.get(18).map(|it| it.rotate_left(18)).unwrap_or(18);
    sum = sum.wrapping_mul(31) ^ words.get(19).map(|it| it.rotate_left(19)).unwrap_or(19);
    sum = sum.wrapping_mul(31) ^ words.get(20).map(|it| it.rotate_left(20)).unwrap_or(20);
    sum = sum.wrapping_mul(31) ^ words.get(21).map(|it| it.rotate_left(21)).unwrap_or(21);
    sum = sum.wrapping_mul(31) ^ words.get(22).map(|it| it.rotate_left(22)).unwrap_or(22);
    sum = sum.wrapping_mul(31) ^ words.get(23).map(|it| it.rotate_left(23)).unwrap_or(23);
    sum = sum.wrapping_mul(31) ^ words.get(24).map(|it| it.rotate_left(24)).unwrap_or(24);
    sum = sum.wrapping_mul(31) ^ words.get(25).map(|it| it.rotate_left(25)).unwrap_or(25);
    sum = sum.wrapping_mul(31) ^ words.get(26).map(|it| it.rotate_left(26)).unwrap_or(26);
    sum = sum.wrapping_mul(31) ^ words.get(27).map(|it| it.rotate_left(27)).unwrap_or(27);
    sum = sum.wrapping_mul(31) ^ words.get(28).map(|it| it.rotate_left(28)).unwrap_or(28);
    sum = sum.wrapping_mul(31) ^ words.get(29).map(|it| it.rotate_left(29)).unwrap_or(29);
    sum = sum.wrapping_mul(31) ^ words.get(30).map(|it| it.rotate_left(30)).unwrap_or(30);
    sum = sum.wrapping_mul(31) ^ words.get(31).map(|it| it.rotate_left(31)).unwrap_or(31);
    sum = sum.wrapping_mul(31) ^ words.get(32).map(|it| it.rotate_left(32)).unwrap_or(32);
    sum = sum.wrapping_mul(31) ^ words.get(33).map(|it| it.rotate_left(33)).unwrap_or(33);
    sum = sum.wrapping_mul(31) ^ words.get(34).map(|it| it.rotate_left(34)).unwrap_or(34);
    sum = sum.wrapping_mul(31) ^ words.get(35).map(|it| it.rotate_left(35)).unwrap_or(35);
    sum = sum.wrapping_mul(31) ^ words.get(36).map(|it| it.rotate_left(36)).unwrap_or(36);
    sum = sum.wrapping_mul(31) ^ words.get(37).map(|it| it.rotate_left(37)).unwrap_or(37);
    sum = sum.wrapping_mul(31) ^ words.get(38).map(|it| it.rotate_left(38)).unwrap_or(38);
    sum = sum.wrapping_mul(31) ^ words.get(39).map(|it| it.rotate_left(39)).unwrap_or(39);
    sum = sum.wrapping_mul(31) ^ words.get(40).map(|it| it.rotate_left(40)).unwrap_or(40);
    sum = sum.wrapping_mul(31) ^ words.get(41).map(|it| it.rotate_left(41)).unwrap_or(41);
    sum = sum.wrapping_mul(31) ^ words.get(42).map(|it| it.rotate_left(42)).unwrap_or(42);
    sum = sum.wrapping_mul(31) ^ words.get(43).map(|it| it.rotate_left(43)).unwrap_or(43);
    sum = sum.wrapping_mul(31) ^ words.get(44).map(|it| it.rotate_left(44)).unwrap_or(44);
    sum = sum.wrapping_mul(31) ^ words.get(45).map(|it| it.rotate_left(45)).unwrap_or(45);
    sum = sum.wrapping_mul(31) ^ words.get(46).map(|it| it.rotate_left(46)).unwrap_or(46);
    sum = sum.wrapping_mul(31) ^ words.get(47).map(|it| it.rotate_left(47)).unwrap_or(47);
    if depth == 0 {
        sum
    } else {
        sum.wrapping_add(level(depth - 1, here, frame, words))
    }
}

/// What the levels sum to, and whether a frame of `level` is under 2k.
pub fn run() -> (u64, bool) {
    let mut frame = 0;
    let words: Vec<u64> = (0..40).map(|it| it * 0x9e37_79b9).collect();
    let sum = level(3, 0, &mut frame, black_box(&words));
    (sum, frame < 2048)
}
