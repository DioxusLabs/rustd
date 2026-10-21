//! `let x = e;` writes `e` straight into `x`. What `e` reads, drops, or never finishes making
//! has to come out as it does through a temporary: a binding it shadows is read before `x` is
//! written, its temporaries end with the statement, and a value it unwinds out of is dropped
//! without `x`.

use std::cell::RefCell;
use std::panic;

thread_local! {
    static LOG: RefCell<Vec<u32>> = const { RefCell::new(Vec::new()) };
}

fn note(event: u32) {
    LOG.with(|it| it.borrow_mut().push(event));
}

struct Loud(u32);

impl Drop for Loud {
    fn drop(&mut self) {
        note(self.0);
    }
}

#[inline(never)]
fn loud(id: u32) -> Loud {
    note(id + 100);
    Loud(id)
}

#[inline(never)]
fn fail(when: bool) -> u32 {
    if when {
        panic!("fails");
    }
    7
}

#[inline(never)]
fn shadowed() -> u32 {
    let pair = (1u32, loud(1));
    let pair = (pair.0 + 10, loud(pair.0 + 1), pair.1);
    note(pair.0);
    pair.0
}

#[inline(never)]
fn temporaries() {
    let length = loud(3).0 + loud(4).0;
    note(length);
    let kept = Loud(loud(5).0 + 1);
    note(kept.0);
}

#[inline(never)]
fn diverging(go: bool) -> u32 {
    let _first = loud(10);
    let second = if go { loud(11) } else { return 0 };
    let third: Loud = match second.0 {
        11 => loud(12),
        _ => panic!("unreachable"),
    };
    second.0 + third.0
}

#[inline(never)]
fn unwound(when: bool) -> Option<u32> {
    panic::catch_unwind(|| {
        let _before = loud(20);
        let pair = (loud(21), fail(when), loud(22));
        pair.1
    })
    .ok()
}

#[inline(never)]
fn moved_or_made(take: bool) {
    let first = loud(30);
    let second = if take { first } else { loud(31) };
    note(second.0);
}

#[inline(never)]
fn in_loop() -> u32 {
    let mut total = 0;
    for i in 0..3 {
        let each = loud(40 + i);
        let mut sum = each.0;
        sum += if i == 1 { continue } else { 1 };
        total += sum;
    }
    total
}

#[inline(never)]
fn nested_closures(x: (u32, u32)) -> u32 {
    let outer = || {
        let inner = || x.1;
        let unread = || match x.0 {
            _ => 3,
        };
        inner() + unread()
    };
    outer()
}

pub fn run() -> (u32, u32, Option<u32>, Option<u32>, u32, u32, Vec<u32>) {
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| ()));
    let shadowed = shadowed();
    temporaries();
    let diverged = diverging(false) + diverging(true);
    let (unwound, finished) = (unwound(true), unwound(false));
    moved_or_made(true);
    moved_or_made(false);
    let looped = in_loop();
    panic::set_hook(hook);
    (
        shadowed,
        diverged,
        unwound,
        finished,
        looped,
        nested_closures((5, 6)),
        LOG.with(|it| it.take()),
    )
}
