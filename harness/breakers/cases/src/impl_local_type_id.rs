//! Local errors in bytecheck and rkyv methods need their written impl's DefPathHash.
//! RUSTFLAGS="-C link-dead-code -C opt-level=3" removes rustc's fallback TypeId shims.

use foreign::local_method_ids::{self, Holder, LocalId};

pub fn run() -> (bool, bool, bool, [std::any::TypeId; 2]) {
    let trait_id = <str as LocalId<_>>::id(|| 0u8);
    let inherent_id = Holder::id(|| 0u16);
    (
        trait_id == local_method_ids::trait_reference(),
        inherent_id == local_method_ids::inherent_reference(),
        trait_id != inherent_id,
        [trait_id, inherent_id],
    )
}
