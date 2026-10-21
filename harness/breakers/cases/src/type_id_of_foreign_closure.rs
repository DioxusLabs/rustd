//! `codex_otel` asks for `TypeId`s of captureless closures in generic functions from crates rustc builds.

use foreign::typeids::closures;
use std::{
    any::{Any, TypeId},
    future::Future,
    task::{Context, Poll, Waker},
};

struct Local;

fn id<T: Any>(value: T) -> (TypeId, bool) {
    let type_id = TypeId::of::<T>();
    let value: Box<dyn Any> = Box::new(value);
    (type_id, value.downcast::<T>().is_ok())
}

fn poll<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    let mut context = Context::from_waker(Waker::noop());
    match future.as_mut().poll(&mut context) {
        Poll::Ready(result) => result,
        Poll::Pending => unreachable!(),
    }
}

pub fn run() -> ((TypeId, bool), (TypeId, bool), (TypeId, bool), (TypeId, bool), (TypeId, bool), (TypeId, bool), (TypeId, bool)) {
    (
        id(closures::generic::<Local>()),
        id(closures::second::<Local>()),
        id(closures::nested::<Local>()),
        id(closures::once::<Local>()),
        id(closures::mutable::<Local>()),
        id(closures::Factory::<Local>::inherent()),
        id(poll(closures::asynchronous::<Local>())),
    )
}
