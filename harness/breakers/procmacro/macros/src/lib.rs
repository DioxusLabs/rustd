//! Macros that give tokens only a proc macro can make.

use proc_macro::{Delimiter, Group, Literal, Punct, Spacing, TokenStream, TokenTree};

#[proc_macro]
pub fn key_method(input: TokenStream) -> TokenStream {
    format!(
        "impl {input} {{ fn key(&self) -> u32 {{ use foreign::keys::Key; self.value.key() }} }}"
    )
    .parse()
    .unwrap()
}

/// Three negative numbers, each one literal token: `(-1, -20i16, -1.5,)`.
#[proc_macro]
pub fn negative_numbers(_: TokenStream) -> TokenStream {
    let parsed: Literal = "-20i16".parse().expect("a negative number is a literal");
    let numbers = [Literal::i8_unsuffixed(-1), parsed, Literal::f32_unsuffixed(-1.5)];
    let mut tuple = TokenStream::new();
    for number in numbers {
        tuple.extend([TokenTree::from(number), TokenTree::from(Punct::new(',', Spacing::Alone))]);
    }
    TokenTree::from(Group::new(Delimiter::Parenthesis, tuple)).into()
}
