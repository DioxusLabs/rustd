//! Declarations and generic code supplied by a crate left to rustc.

unsafe extern "C" {
    pub fn abs(value: i32) -> i32;
    #[link_name = "labs"]
    pub fn long_abs(value: i64) -> i64;
}

mod callsites {
    macro_rules! site {
        ($step:expr) => {{
            static SITE: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
            SITE.fetch_add($step, std::sync::atomic::Ordering::Relaxed)
        }};
    }
    pub(crate) use site;
}

use crate::{callsites as sites};

pub struct Callsite<T>(pub T);

impl<T> Callsite<T> {
    pub fn visit(&self) -> (u32, u32, u32) {
        let first = crate::callsites::site!(1);
        let second = sites::site!(2);
        let closure = || sites::site!(3);
        (first, second, closure())
    }
}

pub fn visit_callsites() -> (u32, u32, u32) {
    Callsite(0u8).visit()
}

pub use reexports::Issue;

mod reexports {
    pub use items::Issue;
    pub(crate) use items::*;

    mod items {
        pub use super::defs::*;
    }

    mod defs {
        pub struct Issue {
            pub value: u32,
        }

        impl Issue {
            pub fn value(self) -> u32 {
                self.value
            }
        }
    }
}
