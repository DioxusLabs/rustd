//! A zero-length `&str` can share an address with its adjacent slice allocation. Treating that
//! address as the string's allocation can memoize the slice before its relocations are visited.

#[derive(Debug)]
pub struct Dir<'a> {
    path: &'a str,
    entries: &'a [Entry<'a>],
}

#[derive(Debug)]
pub enum Entry<'a> {
    Dir(Dir<'a>),
    File(&'a str, &'a [u8]),
}

const C: Dir = Dir {
    path: "",
    entries: &[
        Entry::File("a", b"hi"),
        Entry::Dir(Dir {
            path: "",
            entries: &[Entry::File("s/b", b"yo")],
        }),
    ],
};

#[derive(Debug)]
struct Z<'a> {
    unit: &'a (),
    names: &'a [&'a str],
}

const ZST: Z = Z { unit: &(), names: &["a", "b"] };

pub fn run() -> (String, String) {
    (format!("{C:?}"), format!("{ZST:?}"))
}
