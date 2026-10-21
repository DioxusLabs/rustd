use std::hint::black_box;
use std::time::{Duration, Instant};

#[inline(never)]
fn mix(mut value: u64) -> u64 {
    for _ in 0..4096 {
        value = black_box(value.wrapping_mul(6364136223846793005).wrapping_add(1));
    }
    value
}

#[inline(never)]
pub fn run() -> u64 {
    let start = Instant::now();
    let mut value = black_box(1);
    while start.elapsed() < Duration::from_millis(250) {
        value = mix(value);
    }
    black_box(value)
}
