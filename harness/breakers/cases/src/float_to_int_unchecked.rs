//! num-traits's `ToPrimitive` for floats checks the range and then casts with
//! `to_int_unchecked`, whose intrinsic the daemon did not lower, so none of its tests linked.

#[inline(never)]
fn unchecked(value: f64) -> (i8, u16, i32, u64, i128) {
    // SAFETY: every value given is in range of every type.
    unsafe {
        (
            value.to_int_unchecked(),
            value.to_int_unchecked(),
            (-value).to_int_unchecked(),
            value.to_int_unchecked(),
            (-value).to_int_unchecked(),
        )
    }
}

pub fn run() -> String {
    format!("{:?} {:?}", unchecked(std::hint::black_box(42.9)), unchecked(0.5))
}
