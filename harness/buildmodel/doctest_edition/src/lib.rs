/// An example of another edition than the library's. rustdoc builds it alone; rustd builds the
/// examples of a library in one crate of the library's edition and fails it, saying so.
///
/// ```rust,edition2015
/// let async = app::double(3);
/// assert_eq!(async, 6);
/// ```
pub fn double(x: i32) -> i32 {
    x * 2
}
