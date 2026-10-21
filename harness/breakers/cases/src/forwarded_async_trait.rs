//! A forwarding RPITIT implementation hides another trait method's opaque return type.
//! Resolving only the outer implementation left the nested future without a layout.

use std::future::Future;
use std::pin::pin;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

trait Service<T>: Send + Sync {
    type Output;
    fn perform(&self, input: T) -> impl Future<Output = Self::Output> + Send;
}

struct Number;

impl Service<u32> for Number {
    type Output = u32;

    async fn perform(&self, input: u32) -> u32 {
        input + 1
    }
}

impl<S: Service<T>, T> Service<T> for Arc<S> {
    type Output = S::Output;

    fn perform(&self, input: T) -> impl Future<Output = Self::Output> + Send {
        self.as_ref().perform(input)
    }
}

impl<S: Service<T>, T> Service<T> for Box<S> {
    type Output = S::Output;

    fn perform(&self, input: T) -> impl Future<Output = Self::Output> + Send {
        self.as_ref().perform(input)
    }
}

async fn invoke<S: Service<u32>>(service: S, input: u32) -> S::Output {
    service.perform(input).await
}

fn ready<T>(future: impl Future<Output = T>) -> T {
    let mut future = pin!(future);
    match future.as_mut().poll(&mut Context::from_waker(Waker::noop())) {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("future was not ready"),
    }
}

pub fn run() -> (u32, u32, u32) {
    (
        ready(invoke(Arc::new(Number), 41)),
        ready(invoke(Arc::new(Box::new(Number)), 82)),
        ready(invoke(Box::new(Arc::new(Arc::new(Number))), 9)),
    )
}
