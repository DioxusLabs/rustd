//! Thread-local labels for connector query attribution, not tracked database state.

use std::cell::{Cell, RefCell};

thread_local! {
    static PHASE: Cell<&'static str> = const { Cell::new("other") };
    static ROOT: RefCell<Option<String>> = const { RefCell::new(None) };
}

pub fn root() -> Option<String> {
    ROOT.with(|root| root.borrow().clone())
}

pub fn with_root<T>(root: Option<String>, f: impl FnOnce() -> T) -> T {
    struct Reset(Option<String>);
    impl Drop for Reset {
        fn drop(&mut self) {
            ROOT.with(|root| *root.borrow_mut() = self.0.take());
        }
    }
    let _reset = Reset(ROOT.with(|value| value.replace(root)));
    f()
}

pub fn current() -> &'static str {
    PHASE.get()
}

pub struct Phase(&'static str);

impl Drop for Phase {
    fn drop(&mut self) {
        PHASE.set(self.0);
    }
}

pub fn enter(label: &'static str) -> Phase {
    Phase(PHASE.replace(label))
}

pub fn run<T>(label: &'static str, f: impl FnOnce() -> T) -> T {
    let _reset = enter(label);
    f()
}

pub fn inherit<T>(f: impl FnOnce() -> T) -> impl FnOnce() -> T {
    let phase = current();
    let root = root();
    move || with_root(root, || run(phase, f))
}

#[cfg(test)]
mod tests {
    #[test]
    fn nested_inherited_and_unwound() {
        assert_eq!(super::current(), "other");
        super::run("apply", || {
            let inherited = super::inherit(|| assert_eq!(super::current(), "apply"));
            std::thread::scope(|scope| scope.spawn(inherited).join().unwrap());
            let result = std::panic::catch_unwind(|| super::run("check", || panic!("cancelled")));
            assert!(result.is_err());
            assert_eq!(super::current(), "apply");
        });
        assert_eq!(super::current(), "other");
    }

    #[test]
    fn roots_are_inherited_and_reset() {
        assert_eq!(super::root(), None);
        super::with_root(Some("crate".into()), || {
            let inherited = super::inherit(|| assert_eq!(super::root().as_deref(), Some("crate")));
            std::thread::scope(|scope| scope.spawn(inherited).join().unwrap());
            let result =
                std::panic::catch_unwind(|| super::with_root(None, || panic!("cancelled")));
            assert!(result.is_err());
            assert_eq!(super::root().as_deref(), Some("crate"));
        });
        assert_eq!(super::root(), None);
    }
}
