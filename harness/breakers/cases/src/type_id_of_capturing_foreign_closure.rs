//! A captured closure's `TypeId` depends on inferred upvars and must remain unsupported.

use foreign::typeids::closures;
use std::any::{Any, TypeId};

struct Local;

fn id<T: Any>(value: T) -> (TypeId, bool) {
    let type_id = TypeId::of::<T>();
    let value: Box<dyn Any> = Box::new(value);
    (type_id, value.downcast::<T>().is_ok())
}

pub fn run() -> (TypeId, bool) {
    id(closures::capturing(Local))
}
