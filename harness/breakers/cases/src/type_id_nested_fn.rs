//! starlark's `UnpackValue::unpack_named_param` declares a function whose body declares the error
//! struct it boxes into an `anyhow::Error`, whose vtable asks for the struct's `TypeId`. rustd
//! found no path for a function declared in a body and refused the hash.

use foreign::typeids::Unpack;
use std::any::{Any, TypeId};

fn id<A: Any>(_: &A) -> TypeId {
    TypeId::of::<A>()
}

struct Unpacker;

impl Unpack for Unpacker {}

pub fn run() -> (TypeId, String) {
    let error = Unpacker::hidden(2);
    (id(&error), format!("{error:?}"))
}
