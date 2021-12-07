//! The different types of `Any` for use in a map.
//!
//! This is based on `std::any`, but goes a little further, with `CloneAny`
//! being a cloneable `Any`. `CloneAnySend`, `CloneAnySync`, and
//! `CloneAnySendSync` further retrict what can be placed in the map with the
//! `Send` and `Sync` bounds.

use std::{any::Any as StdAny, fmt};

#[doc(hidden)]
pub trait CloneToAny {
    /// Clone `self` into a new `Box<CloneAny>` object.
    fn clone_to_any(&self) -> Box<dyn CloneAny>;
}

impl<T: Any + Clone> CloneToAny for T {
    #[inline]
    fn clone_to_any(&self) -> Box<dyn CloneAny> {
        Box::new(self.clone())
    }
}

#[doc(hidden)]
pub trait CloneToAnySend: Send {
    /// Clone `self` into a new `Box<CloneAnySend + Send>` object.
    fn clone_to_any_send(&self) -> Box<dyn CloneAnySend + Send>;
}

impl<T: Any + Send + Clone> CloneToAnySend for T {
    #[inline]
    fn clone_to_any_send(&self) -> Box<dyn CloneAnySend + Send> {
        Box::new(self.clone())
    }
}

#[doc(hidden)]
pub trait CloneToAnySync: Sync {
    /// Clone `self` into a new `Box<CloneAnySync + Sync>` object.
    fn clone_to_any_sync(&self) -> Box<dyn CloneAnySync + Sync>;
}

impl<T: Any + Sync + Clone> CloneToAnySync for T {
    #[inline]
    fn clone_to_any_sync(&self) -> Box<dyn CloneAnySync + Sync> {
        Box::new(self.clone())
    }
}

#[doc(hidden)]
pub trait CloneToAnySendSync: Send + Sync {
    /// Clone `self` into a new `Box<CloneAnySendSync + Send + Sync>` object.
    fn clone_to_any_send_sync(&self) -> Box<dyn CloneAnySendSync + Send + Sync>;
}

impl<T: Any + Send + Sync + Clone> CloneToAnySendSync for T {
    #[inline]
    fn clone_to_any_send_sync(&self) -> Box<dyn CloneAnySendSync + Send + Sync> {
        Box::new(self.clone())
    }
}

macro_rules! define {
    (CloneAny) => {
        /// A type to emulate dynamic typing.
        ///
        /// Every type with no non-`'static` references implements `Any`.
        define!(CloneAny remainder);
    };
    (CloneAnySend) => {
        /// A type to emulate dynamic typing.
        ///
        /// Every type with no non-`'static` references implements `Any`.
        define!(CloneAnySend remainder);
    };
    (CloneAnySync) => {
        /// A type to emulate dynamic typing.
        ///
        /// Every type with no non-`'static` references implements `Any`.
        define!(CloneAnySync remainder);
    };
    (CloneAnySendSync) => {
        /// A type to emulate dynamic typing.
        ///
        /// Every type with no non-`'static` references implements `Any`.
        define!(CloneAnySendSync remainder);
    };
    (Any) => {
        /// A type to emulate dynamic typing with cloning.
        ///
        /// Every type with no non-`'static` references that implements `Clone` implements `Any`.
        define!(Any remainder);
    };
    ($t:ident remainder) => {
        /// See the [`std::any` documentation](https://doc.rust-lang.org/std/any/index.html) for
        /// more details on `Any` in general.
        ///
        /// This trait is not `std::any::Any` but rather a type extending that for this library’s
        /// purposes so that it can be combined with marker traits like
        /// <code><a class=trait title=core::marker::Send
        /// href=http://doc.rust-lang.org/std/marker/trait.Send.html>Send</a></code> and
        /// <code><a class=trait title=core::marker::Sync
        /// href=http://doc.rust-lang.org/std/marker/trait.Sync.html>Sync</a></code>.
        ///
        define!($t trait);
    };
    (CloneAny trait) => {
        /// See also [`Any`](trait.Any.html) for a version without the `Clone` requirement.
        pub trait CloneAny: Any + CloneToAny { }
        impl<T: StdAny + Clone> CloneAny for T { }
    };
    (CloneAnySend trait) => {
        /// See also [`Any`](trait.Any.html) for a version without the `Clone + Send` requirements.
        pub trait CloneAnySend: Any + CloneToAnySend { }
        impl<T: StdAny + Send + Clone> CloneAnySend for T { }
    };
    (CloneAnySync trait) => {
        /// See also [`Any`](trait.Any.html) for a version without the `Clone + Sync` requirements.
        pub trait CloneAnySync: Any + CloneToAnySync { }
        impl<T: StdAny + Sync + Clone> CloneAnySync for T { }
    };
    (CloneAnySendSync trait) => {
        /// See also [`Any`](trait.Any.html) for a version without the `Clone + Send + Sync` requirements.
        pub trait CloneAnySendSync: Any + CloneToAnySendSync { }
        impl<T: StdAny + Send + Sync + Clone> CloneAnySendSync for T { }
    };
    (Any trait) => {
        /// See also [`CloneAny`](trait.CloneAny.html) for a cloneable version of this trait.
        pub trait Any: StdAny { }
        impl<T: StdAny> Any for T { }
    };
}

macro_rules! impl_clone {
    ($t:ty, $method:ident) => {
        impl Clone for Box<$t> {
            #[inline]
            fn clone(&self) -> Box<$t> {
                (**self).$method()
            }
        }
    };
}

// Not public outside the crate.
#[allow(missing_docs, clippy::missing_safety_doc)]
pub trait UncheckedAnyExt: Any {
    unsafe fn downcast_ref_unchecked<T: Any>(&self) -> &T;
    unsafe fn downcast_mut_unchecked<T: Any>(&mut self) -> &mut T;
    unsafe fn downcast_unchecked<T: Any>(self: Box<Self>) -> Box<T>;
}

#[doc(hidden)]
/// A trait for the conversion of an object into a boxed trait object.
pub trait IntoBox<A: ?Sized + UncheckedAnyExt>: Any {
    /// Convert self into the appropriate boxed form.
    fn into_box(self) -> Box<A>;
}

macro_rules! implement {
    ($base:ident, $(+ $bounds:ident)*) => {
        impl fmt::Debug for dyn $base $(+ $bounds)* {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.pad(stringify!($base $(+ $bounds)*))
            }
        }

        impl UncheckedAnyExt for dyn $base $(+ $bounds)* {
            #[inline]
            unsafe fn downcast_ref_unchecked<T>(&self) -> &T {
                &*(self as *const Self as *const T)
            }

            #[inline]
            unsafe fn downcast_mut_unchecked<T>(&mut self) -> &mut T {
                &mut *(self as *mut Self as *mut T)
            }

            #[inline]
            unsafe fn downcast_unchecked<T>(self: Box<Self>) -> Box<T> {
                Box::from_raw(Box::into_raw(self) as *mut T)
            }
        }

        impl<T: $base $(+ $bounds)*> IntoBox<dyn $base $(+ $bounds)*> for T {
            #[inline]
            fn into_box(self) -> Box<dyn $base $(+ $bounds)*> {
                Box::new(self)
            }
        }
    }
}

define!(Any);
implement!(Any,);
implement!(Any, + Send);
implement!(Any, + Sync);
implement!(Any, + Send + Sync);
implement!(CloneAny,);
implement!(CloneAnySend, + Send);
implement!(CloneAnySync, + Sync);
implement!(CloneAnySendSync, + Send + Sync);

define!(CloneAny);
define!(CloneAnySend);
define!(CloneAnySync);
define!(CloneAnySendSync);
impl_clone!(dyn CloneAny, clone_to_any);
impl_clone!((dyn CloneAnySend + Send), clone_to_any_send);
impl_clone!((dyn CloneAnySync + Sync), clone_to_any_sync);
impl_clone!((dyn CloneAnySendSync + Send + Sync), clone_to_any_send_sync);
