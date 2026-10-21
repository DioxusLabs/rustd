//! A blanket future adapter whose associated output requires proving its `Send` bounds.

use std::future::Future;

pub trait Attempt: Sized {
    type Output;
    fn attempt(self) -> impl Future<Output = Result<Self::Output, ()>> + Send;
}

impl<F: Future + Send> Attempt for F
where
    F::Output: Send,
{
    type Output = F::Output;

    async fn attempt(self) -> Result<Self::Output, ()> {
        Ok(self.await)
    }
}
