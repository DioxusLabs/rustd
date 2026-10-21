//! Declarations and generic code supplied by a crate left to rustc.

pub mod keys {
    pub trait Key {
        fn key(&self) -> u32;
    }

    impl Key for u8 {
        fn key(&self) -> u32 {
            *self as u32 + 3
        }
    }
}

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

#[derive(Debug)]
pub struct LocalTypes;

pub mod local_method_ids {
    use std::any::TypeId;

    #[derive(Debug)]
    pub struct Neighbour;

    macro_rules! extra {
        () => {
            impl Neighbour {
                pub fn extra() {}
            }
        };
    }
    extra!();

    pub trait LocalId<T> {
        fn id(value: T) -> TypeId;
    }

    impl<T> LocalId<T> for str {
        #[inline]
        fn id(_: T) -> TypeId {
            struct LocalError;
            TypeId::of::<LocalError>()
        }
    }

    pub struct Holder;

    impl Holder {
        #[inline]
        pub fn id<T>(_: T) -> TypeId {
            struct LocalError;
            TypeId::of::<LocalError>()
        }
    }

    pub fn trait_reference() -> TypeId {
        <str as LocalId<()>>::id(())
    }

    pub fn inherent_reference() -> TypeId {
        Holder::id(())
    }
}

macro_rules! padding {
    () => {
        const _: () = ();
    };
}
padding!();

#[cfg(any())]
const _: () = ();

const _: () = ();

const _: () = {
    struct LocalError;

    impl LocalTypes {
        pub fn first<T>(_: T) -> std::any::TypeId {
            std::any::TypeId::of::<LocalError>()
        }

        pub fn first_reference() -> std::any::TypeId {
            std::any::TypeId::of::<LocalError>()
        }
    }
};

const _: () = {
    struct LocalError;

    impl LocalTypes {
        pub fn second<T>(_: T) -> std::any::TypeId {
            std::any::TypeId::of::<LocalError>()
        }

        pub fn second_reference() -> std::any::TypeId {
            std::any::TypeId::of::<LocalError>()
        }
    }
};

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

pub mod served {
    use std::future::Future;

    pub trait Serve {
        fn serve(&self, step: u32) -> impl Future<Output = u32> + Send;
    }

    pub struct Auto;
    pub struct Other;

    pub struct Logged<T, K = Auto>(pub T, pub K);

    impl<T: Sync> Serve for Logged<T, Auto> {
        async fn serve(&self, step: u32) -> u32 {
            crate::callsites::site!(step)
        }
    }

    impl<T: Sync> Serve for Logged<T, Other> {
        async fn serve(&self, step: u32) -> u32 {
            crate::callsites::site!(step * 100)
        }
    }

    /// rustc's own instance of the method, whose static rustd's shares.
    pub fn served_by_rustc(step: u32) -> u32 {
        crate::ready(Box::pin(Logged(0u8, Auto).serve(step)))
    }
}

/// The output of a future that is ready the first time it is polled.
pub fn ready(mut future: std::pin::Pin<Box<dyn Future<Output = u32> + Send + '_>>) -> u32 {
    use std::task::{Context, Poll, Waker};
    match future.as_mut().poll(&mut Context::from_waker(Waker::noop())) {
        Poll::Ready(it) => it,
        Poll::Pending => unreachable!(),
    }
}

/// Types rustc hashes for `TypeId`s asked for by code rustd compiles.
pub mod typeids {
    use std::any::{Any, TypeId};

    pub enum Status {
        Bad(u32),
    }

    fn id<A: Any>(_: &A) -> TypeId {
        TypeId::of::<A>()
    }

    pub fn ok_id() -> TypeId {
        id(&Ok::<u8, u16>)
    }

    pub fn bad_id() -> TypeId {
        id(&Status::Bad)
    }
}
