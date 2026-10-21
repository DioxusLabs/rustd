//! An expansion can be the only code that names a dependency whose impls are needed.

#[test]
fn generated_key() {
    assert_eq!(procmacro::generated_key(0), 3);
    assert_eq!(procmacro::generated_key(7), 10);
    assert_eq!(procmacro::generated_key(255), 258);
}
