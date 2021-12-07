use super::ToTokens;
use std::borrow::Borrow;
use std::slice;

/// Defines the behavior of types that can be interpolated inside repeating patterns (`#(...)*`).
///
/// ### Which types *do* `Repeat`
///   - [`Iterator<T>`] consumes the iterator, iterating through every element.
///   - <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">`Borrow<[T]>`</a>
/// (includes [`Vec`], [`array`], and [`slice`]) iterates with the [`slice::iter`] method,
/// thus not consuming the original data.
///   - [`ToTokens`], interpolates the variable in every iteration.
///
/// ### Which types *do NOT* `Repeat`
///   - [`IntoIterator`], to avoid ambiguity (Ex. "Which behavior would have been used for [`Vec`],
/// which implements both [`IntoIterator`] and <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">
/// `Borrow<[T]>`</a>?"; "Which behavior would have been used for [`TokenStream`], which implements both
/// [`IntoIterator`] and [`ToTokens`]?"). To use the iterator, you may call [`IntoIterator::into_iter`]
/// explicitly.
///   - Ambiguous types that implement at least two of the `Repeat` traits. In the very unlikely case
/// this happens, disambiguate the type by wrapping it under some structure that only implements the
/// trait you desire to use.
///
/// [`Iterator<T>`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
/// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
/// [`array`]: https://doc.rust-lang.org/std/primitive.array.html
/// [`slice`]: https://doc.rust-lang.org/std/slice/index.html
/// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
/// [`ToTokens`]: https://docs.rs/proc-quote/0/proc_quote/trait.ToTokens.html
/// [`IntoIterator`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html
/// [`IntoIterator::into_iter`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html#tymethod.into_iter
pub trait Repeat<T: Iterator>: private::Sealed<T> {
    // Long name to avoid collision
    // TODO(Blocked on #7): rename to `as_repeat` once collision is solved
    #[allow(non_snake_case)]
    #[doc(hidden)]
    fn __proc_quote__as_repeat(self) -> T;
}

mod private {
    use super::*;
    pub trait Sealed<T> {}

    impl<T, I: Iterator<Item = T>> Sealed<I> for I {}
    impl<'a, T: 'a, S: Borrow<[T]>> Sealed<slice::Iter<'a, T>> for &'a S {}
    impl<'a, T: ToTokens + 'a> Sealed<ToTokensRepeat<'a, T>> for &'a T {}
}

/// Types that implement `Iterator` may be used in repeating patterns.
///
/// They, will be consumed, so they can only be used in one pattern.
impl<T, I: Iterator<Item = T>> Repeat<I> for I {
    fn __proc_quote__as_repeat(self) -> I {
        self
    }
}

/// Types that implement `Borrow<[T]>` may be used in repeating patterns.
///
/// This includes, but is not necessarily limited to, `Vec`, `array` and `slice`.
///
/// They, will not be consumed. Instead `slice::iter` will be implicitly called.
impl<'a, T: 'a, S: Borrow<[T]>> Repeat<slice::Iter<'a, T>> for &'a S {
    fn __proc_quote__as_repeat(self) -> slice::Iter<'a, T> {
        (*self).borrow().iter()
    }
}

/// Types that implement `ToTokens` may be used in repeating patterns.
///
/// The variable will be interpolated in every iteration.
impl<'a, T: ToTokens + 'a> Repeat<ToTokensRepeat<'a, T>> for &'a T {
    fn __proc_quote__as_repeat(self) -> ToTokensRepeat<'a, T> {
        ToTokensRepeat(self)
    }
}

/// Struct that wraps a reference to `ToTokens` in order to use it in repeating patterns.
pub struct ToTokensRepeat<'a, T: ToTokens + 'a>(&'a T);
impl<'a, T: ToTokens + 'a> Iterator for ToTokensRepeat<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0)
    }
}
