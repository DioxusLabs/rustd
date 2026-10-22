//! typetag and inventory register each impl from a constructor that a macro writes in a
//! `const _: () = { .. }`, so two impls in one function give two `__ctor`s of one path. Neither
//! was given rustc's symbol, so rustc's ran at startup and filled rustc's copy of a registry
//! that rustd's code never read.

use std::sync::atomic::{AtomicUsize, Ordering};

trait Registry {
    fn registry() -> &'static AtomicUsize;
}

impl Registry for fn(&mut dyn std::fmt::Write) {
    fn registry() -> &'static AtomicUsize {
        static REGISTERED: AtomicUsize = AtomicUsize::new(0);
        &REGISTERED
    }
}

macro_rules! submit {
    ($value:expr) => {
        const _: () = {
            extern "C" fn __ctor() {
                <fn(&mut dyn std::fmt::Write) as Registry>::registry()
                    .fetch_add($value, Ordering::Relaxed);
            }
            #[used]
            #[cfg_attr(any(target_os = "linux", target_os = "android"), unsafe(link_section = ".init_array"))]
            #[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__mod_init_func"))]
            #[cfg_attr(windows, unsafe(link_section = ".CRT$XCU"))]
            static __CTOR: extern "C" fn() = __ctor;
        };
    };
}

pub fn run() -> usize {
    submit!(1);
    submit!(10);
    <fn(&mut dyn std::fmt::Write) as Registry>::registry().load(Ordering::Relaxed)
}
