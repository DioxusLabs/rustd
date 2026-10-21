//! A future keeps, in each of its states, only what is used after that await, as rustc lays it
//! out. What goes wrong there shows when a future is dropped half way: a local dropped twice or
//! not at all, one read from memory another has taken. Each future here is polled a number of
//! times and then dropped, and says what it dropped.
//!
//! The size of each is told too. A local a part of which is moved out (`in_parts`) had a word
//! of drop flags in rustd's future, where a byte holds the few bits it needs.

use std::cell::RefCell;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

type Log = Rc<RefCell<Vec<String>>>;

struct Noisy(&'static str, Log);

impl Drop for Noisy {
    fn drop(&mut self) {
        self.1.borrow_mut().push(format!("drop {}", self.0));
    }
}

/// Pending once, then ready.
struct Once(bool);

impl Future for Once {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if std::mem::replace(&mut self.0, true) { Poll::Ready(()) } else { Poll::Pending }
    }
}

fn pause() -> Once {
    Once(false)
}

async fn in_turn(log: Log) -> usize {
    let first = Noisy("first", log.clone());
    pause().await;
    let second = Noisy("second", log.clone());
    drop(first);
    pause().await;
    let third = Noisy("third", log.clone());
    pause().await;
    second.0.len() + third.0.len()
}

async fn in_parts(log: Log) -> usize {
    let pair = (Noisy("left", log.clone()), Noisy("right", log.clone()));
    pause().await;
    let left = pair.0;
    pause().await;
    drop(left);
    pause().await;
    pair.1 .0.len()
}

async fn perhaps(log: Log, yes: bool) -> usize {
    let held;
    if yes {
        held = Noisy("held", log.clone());
        pause().await;
    } else {
        pause().await;
        held = Noisy("late", log.clone());
    }
    pause().await;
    held.0.len()
}

async fn in_loop(log: Log) -> usize {
    let mut sum = 0;
    let mut numbers = [1usize, 2, 3];
    for round in 0..3 {
        let noisy = Noisy("round", log.clone());
        let slot = &mut numbers[round];
        pause().await;
        *slot += round;
        sum += *slot + noisy.0.len();
    }
    pause().await;
    sum + numbers.iter().sum::<usize>()
}

async fn nested(log: Log) -> usize {
    let outer = Noisy("outer", log.clone());
    let inner = in_turn(log.clone()).await;
    let buffer = [inner as u8; 40];
    pause().await;
    outer.0.len() + buffer.iter().map(|&it| it as usize).sum::<usize>()
}

/// The value moved out of the `Some` leaves nothing in the `Option` to keep or drop.
async fn unwrapped(log: Log) -> usize {
    let maybe = Some(Noisy("unwrapped", log.clone()));
    let Some(noisy) = maybe else { return 0 };
    pause().await;
    let again = Some(Noisy("again", log.clone()));
    if let Some(inner) = again {
        pause().await;
        return noisy.0.len() + inner.0.len();
    }
    0
}

async fn panics(log: Log) -> usize {
    let before = Noisy("before", log.clone());
    pause().await;
    let after = Noisy("after", log.clone());
    if before.0.len() == 6 {
        panic!("in poll");
    }
    pause().await;
    after.0.len()
}

/// Polls the future so many times, drops it, and tells what happened in order.
fn drive<F: Future<Output = usize>>(name: &str, polls: usize, make: impl FnOnce(Log) -> F) -> String {
    let log = Log::default();
    let mut future = Box::pin(make(log.clone()));
    let mut cx = Context::from_waker(Waker::noop());
    for _ in 0..polls {
        match catch_unwind(AssertUnwindSafe(|| future.as_mut().poll(&mut cx))) {
            Ok(Poll::Ready(value)) => {
                log.borrow_mut().push(format!("ready {value}"));
                break;
            }
            Ok(Poll::Pending) => log.borrow_mut().push("pending".to_owned()),
            Err(_) => {
                log.borrow_mut().push("panicked".to_owned());
                break;
            }
        }
    }
    let size = std::mem::size_of_val(&*future);
    drop(future);
    let log = log.borrow();
    format!("{name}/{polls} ({size} bytes): {}", log.join(", "))
}

pub fn run() -> Vec<String> {
    let mut out = Vec::new();
    for polls in 0..6 {
        out.push(drive("in_turn", polls, in_turn));
        out.push(drive("in_parts", polls, in_parts));
        out.push(drive("perhaps", polls, |log| perhaps(log, true)));
        out.push(drive("perhaps not", polls, |log| perhaps(log, false)));
        out.push(drive("in_loop", polls, in_loop));
        out.push(drive("nested", polls, nested));
        out.push(drive("unwrapped", polls, unwrapped));
        out.push(drive("panics", polls, panics));
    }
    out
}
