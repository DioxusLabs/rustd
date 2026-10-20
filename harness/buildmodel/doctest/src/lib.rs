//! The crate's own docs.
//!
//! ```
//! assert_eq!(app::double(1), 2);
//! ```
#![doc = include_str!("../docs/more.md")]

/// Doubles.
///
/// ```
/// assert_eq!(app::double(2), 4);
/// ```
///
/// ```should_panic
/// assert_eq!(app::double(2), 5);
/// ```
///
/// ```no_run
/// loop {
///     app::double(2);
/// }
/// ```
///
/// ```compile_fail
/// let _: String = app::double(2);
/// ```
///
/// ```ignore
/// this is not rust
/// ```
///
/// ```text
/// not a test
/// ```
///
/// ```
/// # let hidden = app::double(4);
/// assert_eq!(hidden, 8);
/// ##[derive(Debug)]
/// struct Shown;
/// ```
///
/// ```
/// use app::double;
/// fn main() {
///     println!("printed {}", double(5));
/// }
/// ```
///
/// ```
/// let n: u32 = "7".parse()?;
/// assert_eq!(app::double(n), 14);
/// # Ok::<(), std::num::ParseIntError>(())
/// ```
///
/// A failing one:
///
/// ```
/// assert_eq!(app::double(2), 7, "wrong on purpose");
/// ```
///
///     // indented code is a test too
///     assert_eq!(app::double(6), 12);
pub fn double(n: u32) -> u32 {
    n * 2
}

/// A type.
pub struct Counter {
    /// A field.
    ///
    /// ```
    /// let c = app::Counter { n: 1 };
    /// assert_eq!(c.n, 1);
    /// ```
    pub n: u32,
}

impl Counter {
    /// Bumps.
    ///
    /// ```
    /// #![allow(dead_code)]
    /// extern crate app as other;
    /// let mut c = other::Counter { n: 1 };
    /// c.bump();
    /// assert_eq!(c.n, 2);
    /// ```
    pub fn bump(&mut self) {
        self.n += 1;
    }
}

pub mod inner {
    //! Inner module docs.
    //!
    //! ```
    //! assert_eq!(app::inner::triple(2), 6);
    //! ```

    /** Block comment.

    ```
    assert_eq!(app::inner::triple(3), 9);
    ```
    */
    pub fn triple(n: u32) -> u32 {
        n * 3
    }

    /// A trait.
    pub trait Named {
        /// Its name.
        ///
        /// ~~~
        /// use app::inner::Named;
        /// assert_eq!(<u8 as Named>::name(), "u8");
        /// ~~~
        fn name() -> &'static str;
    }

    impl Named for u8 {
        /// ```
        /// use app::inner::Named;
        /// assert_eq!(u8::name().len(), 2);
        /// ```
        fn name() -> &'static str {
            "u8"
        }
    }
}

/// An enum.
pub enum Kind {
    /// ```
    /// let _ = app::Kind::One;
    /// ```
    One,
}

/// ```
/// assert_eq!(app::twice!(4), 8);
/// ```
#[macro_export]
macro_rules! twice {
    ($e:expr) => {
        $crate::double($e)
    };
}
