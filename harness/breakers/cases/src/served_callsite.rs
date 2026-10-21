//! A static in the `async` method of an impl in a crate left to rustc, for a type whose last
//! argument is its parameter's default (rama's `TlsConnector<S, ConnectorKindAuto>` with
//! tracing's `__CALLSITE`). rustc leaves that argument out of the symbol; rustd named it, found
//! no rustc symbol and refused the writable static.

use foreign::ready;
use foreign::served::{Auto, Logged, Other, Serve, served_by_rustc};

/// Of this crate, so that no copy rustc built of the method can stand in for rustd's.
struct Local;

pub fn run() -> (u32, u32, u32, u32, u32) {
    let (auto, other) = (Logged(Local, Auto), Logged(Local, Other));
    let first = ready(Box::pin(auto.serve(2)));
    let theirs = served_by_rustc(5);
    let again = ready(Box::pin(auto.serve(3)));
    (first, theirs, again, ready(Box::pin(other.serve(1))), ready(Box::pin(other.serve(2))))
}
