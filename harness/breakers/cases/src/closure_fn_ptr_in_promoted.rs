//! rustc promotes a borrow with a closure-to-function-pointer cast, but rust-analyzer left it
//! in the frame, where the returned reference dangled after the stack was reused.

struct VT3 {
    f: fn(u8) -> u8,
    n: u8,
}

const fn new3<T>() -> &'static VT3 {
    &VT3 { f: |x| x + 1, n: 3 }
}

#[inline(never)]
fn clobber() -> u64 {
    let a = [7u64; 64];
    std::hint::black_box(a).iter().sum()
}

pub fn run() -> (u8, u8) {
    let v = new3::<u8>();
    clobber();
    ((v.f)(1), v.n)
}
