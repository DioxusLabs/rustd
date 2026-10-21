//! rustc resolves this at depth 32, including with its next solver. rustd exhausted its
//! solver depth while normalizing the adapter's output, leaving the async body's locals
//! untyped and reporting an unknown coroutine layout instead.
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

async fn read(value: &Deep) -> Result<u32, ()> {
    let value = ready(value).attempt().await?;
    Ok(value.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0)
}

#[test]
fn resolves_deep_future_output() {
    let value = four(four(four(four(four(four(42))))));
    let mut future = pin!(read(&value));
    assert_eq!(future.as_mut().poll(&mut Context::from_waker(Waker::noop())), Poll::Ready(Ok(42)),);
}
