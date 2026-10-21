use foreign::default_callsites::{DefaultCallsites, served_async_callsite, served_callsite};
use foreign::ready;

struct Local;

impl DefaultCallsites for Local {}

pub fn run() -> (u32, u32, u32, u32, u32, u32, u32, u32, u32) {
    let local = Local;
    (
        local.visit(true, 1),
        served_callsite(true, 1),
        local.visit(false, 2),
        served_callsite(false, 2),
        ready(Box::pin(local.visit_async(true, 3))),
        ready(Box::pin(served_async_callsite(true, 3))),
        ready(Box::pin(local.visit_async(false, 4))),
        ready(Box::pin(served_async_callsite(false, 4))),
        local.visit(true, 5),
    )
}
