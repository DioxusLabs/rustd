//! Salsa's supertype entries chain iterators returned by trait methods.

trait Entries {
    fn entries() -> impl Iterator<Item = u32>;
}

struct Leaf;
impl Entries for Leaf {
    fn entries() -> impl Iterator<Item = u32> {
        [1, 2].into_iter()
    }
}

struct Pair;
impl Entries for Pair {
    fn entries() -> impl Iterator<Item = u32> {
        std::iter::empty().chain(Leaf::entries()).chain(Leaf::entries())
    }
}

pub fn run() -> Vec<u32> {
    let mut values: Vec<_> = Pair::entries().collect();
    values.extend(Forward::<Pair>::entries());
    values.extend(Forward::<Empty>::entries());
    values
}

struct Empty;
impl Entries for Empty {
    fn entries() -> impl Iterator<Item = u32> {
        std::iter::empty()
    }
}

struct Forward<T>(std::marker::PhantomData<T>);
impl<T: Entries> Entries for Forward<T> {
    fn entries() -> impl Iterator<Item = u32> {
        T::entries()
    }
}
