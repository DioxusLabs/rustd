//! Nested adapters infer successfully, but selecting the concrete blanket implementation
//! for their opaque return types can exhaust the post-analysis solver depth.
#![recursion_limit = "32"]

use async_solver_depth::Attempt;
use std::future::{Future, ready};
use std::pin::pin;
use std::task::{Context, Poll, Waker};

struct Nest<T>(T);
type Four<T> = Nest<Nest<Nest<Nest<T>>>>;
type Deep = Four<Four<Four<Four<Four<Four<u32>>>>>>;

fn four<T>(value: T) -> Four<T> {
    Nest(Nest(Nest(Nest(value))))
}

async fn run(value: &Deep) -> u32 {
    let value = ready(value)
        .attempt()
        .attempt()
        .attempt()
        .attempt()
        .await
        .unwrap()
        .unwrap()
        .unwrap()
        .unwrap();
    value.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0
}

#[test]
fn selects_deep_future() {
    let value = four(four(four(four(four(four(42))))));
    let mut future = pin!(run(&value));
    assert_eq!(future.as_mut().poll(&mut Context::from_waker(Waker::noop())), Poll::Ready(42));
}
