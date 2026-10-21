//! tonic maps a request stream with `Ok` and asks for the stream's `TypeId`, which hashes the
//! constructor's fn item. rustd hashed only the fn items of functions and refused.

use foreign::typeids::{self, Status};
use std::any::{Any, TypeId};

fn id<A: Any>(_: &A) -> TypeId {
    TypeId::of::<A>()
}

struct Wrap(u8);

enum Local {
    One(u16),
}

pub fn run() -> ([TypeId; 5], [bool; 2]) {
    let ids = [id(&Ok::<u8, u16>), id(&Some::<u32>), id(&Wrap), id(&Local::One), id(&Status::Bad)];
    (ids, [ids[0] == typeids::ok_id(), ids[4] == typeids::bad_id()])
}
