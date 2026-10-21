//! What a proc macro gives that source text cannot.

struct Item {
    value: u8,
}

macros::key_method!(Item);

pub fn generated_key(value: u8) -> u32 {
    Item { value }.key()
}

/// The name of a number, matched against constants a macro wrote as negative literals.
pub fn name(number: i8) -> &'static str {
    const NUMBERS: (i8, i16, f32) = macros::negative_numbers!();
    const MINUS_ONE: i8 = NUMBERS.0;
    match number {
        MINUS_ONE => "minus one",
        0 => "zero",
        _ => "other",
    }
}

pub fn numbers() -> (i8, i16, f32) {
    macros::negative_numbers!()
}

/// What the records of `sized` hold, and how large one is.
pub fn records() -> (Vec<u32>, usize) {
    let records = sized::records();
    let held = records.iter().map(|record| match record {
        sized::Record::Short(word) => *word,
        sized::Record::Long(body) => body.words.iter().sum(),
    });
    (held.collect(), std::mem::size_of::<sized::Record>())
}
