//! rkyv's bytecheck errors are declared in unnamed constants but need rustc-compatible IDs.

use foreign::LocalTypes;

pub fn run() -> (bool, bool, bool, [std::any::TypeId; 2]) {
    let first = LocalTypes::first(|| 0u8);
    let second = LocalTypes::second(|| 0u16);
    (
        first == LocalTypes::first_reference(),
        second == LocalTypes::second_reference(),
        first != second,
        [first, second],
    )
}
