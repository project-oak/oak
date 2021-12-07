//! Crate for safe conversion between units of memory.

#![deny(missing_docs)]
#![no_std]

use core::mem;
use core::ops;

macro_rules! impl_byte_size {
    ( $name:ident , $byte_size:expr ) => {
        impl ByteSize for $name {
            #[inline]
            fn byte_size() -> Bytes {
                Bytes($byte_size)
            }
        }
    }
}

macro_rules! impl_from_bytes {
    ( $name:ident ) => {
        impl From<$name> for Bytes {
            #[inline]
            fn from(x: $name) -> Bytes {
                Bytes(x.0 * $name::byte_size().0)
            }
        }
    }
}

macro_rules! impl_ops {
    ( $name:ident ) => {
        impl<T: Into<Bytes>> RoundUpTo<$name> for T {
            fn round_up_to(self) -> $name {
                let bytes: Bytes = self.into();
                $name(round_up_to(bytes.0, $name::byte_size().0))
            }
        }

        impl<T: Into<Self>> ops::Add<T> for $name {
            type Output = Self;

            #[inline]
            fn add(self, rhs: T) -> Self {
                $name(self.0 + rhs.into().0)
            }
        }

        impl<T: Into<Self>> ops::Sub<T> for $name {
            type Output = Self;

            #[inline]
            fn sub(self, rhs: T) -> Self {
                $name(self.0 - rhs.into().0)
            }
        }

        impl<T: Into<Self>> ops::Mul<T> for $name {
            type Output = Self;

            #[inline]
            fn mul(self, rhs: T) -> Self {
                $name(self.0 * rhs.into().0)
            }
        }

        impl<T: Into<Self>> ops::Div<T> for $name {
            type Output = Self;

            #[inline]
            fn div(self, rhs: T) -> Self {
                $name(self.0 / rhs.into().0)
            }
        }
    }
}

macro_rules! define_newtype {
    (
        $( #[$attr:meta] )*
        newtype $name:ident = $t:ty;
    ) => {
        $( #[$attr] )*
        pub struct $name(pub $t);
    }
}

macro_rules! define_unit {
    (
        $( #[$attr:meta] )*
        newtype $name:ident is bytes = $byte_size:expr;
    ) => {
        define_newtype! {
            $( #[$attr] )*
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
            newtype $name = usize;
        }
        impl_byte_size!($name, $byte_size);
        impl_from_bytes!($name);
        impl_ops!($name);
    }
}

/// Returns the size of a type in [`Bytes`].
///
/// # Example
///
/// ```rust
/// # use memory_units::*;
/// #[repr(C)]
/// struct Hello {
///     a: u32,
///     b: u32,
/// }
///
/// assert_eq!(size_of::<Hello>(), Bytes(4 + 4));
/// ```
///
/// [`Bytes`]: struct.Bytes.html
#[inline]
pub fn size_of<T>() -> Bytes {
    Bytes(mem::size_of::<T>())
}

/// A trait defining round up conversion between various memory units.
///
/// # Example
///
/// ```rust
/// # use memory_units::*;
/// // `bytes` contains the size of 1 memory page in bytes.
/// let mut bytes: Bytes = Pages(1).into();
///
/// // Adding 1 to `bytes` makes it larger than the single page.
/// bytes.0 += 1;
/// let pages: Pages = bytes.round_up_to();
/// assert_eq!(pages, Pages(2));
/// ```
pub trait RoundUpTo<T> {
    /// Returns minimum number of `T` to fit amount of space occupied by `self`.
    fn round_up_to(self) -> T;
}

#[inline]
pub(crate) fn round_up_to(n: usize, divisor: usize) -> usize {
    (n + divisor - 1) / divisor
}

/// A trait defining the size, in bytes, of one unit of `Self`.
///
/// # Example
///
/// ```rust
/// # use memory_units::*;
/// println!("The size of one word in bytes is {}.", Words::byte_size().0);
/// ```
pub trait ByteSize {
    /// The size, in bytes, of a single unit of `Self`.
    fn byte_size() -> Bytes;
}


define_newtype! {
    /// Memory size specified in bytes.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    newtype Bytes = usize;
}
impl_byte_size!(Bytes, 1);
impl_ops!(Bytes);

pub mod wasm32 {
    //! WebAssembly-specific sizes and units.

    use super::*;
    use core::ops;

    define_unit! {
        /// Memory size specified in `wasm32` words.
        newtype Words is bytes = 4;
    }

    define_unit! {
        /// Memory size specified in WebAssembly [memory pages][memory page].
        ///
        /// [memory page]: https://en.wikipedia.org/wiki/Page_(computer_memory)
        newtype Pages is bytes = 65536;
    }
}

#[cfg(target_arch = "wasm32")]
pub mod target {
    //! Sizes and units for the current compilation target.

    pub use wasm32::*;
}

#[cfg(not(target_arch = "wasm32"))]
pub mod target {
    //! Sizes and units for the current compilation target.

    use super::*;
    use core::mem;
    use core::ops;

    define_unit! {
        /// Memory size specified in words.
        newtype Words is bytes = mem::size_of::<usize>();
    }

    define_unit! {
        /// Memory size specified in [memory pages][memory page].
        ///
        /// [memory page]: https://en.wikipedia.org/wiki/Page_(computer_memory)
        newtype Pages is bytes = 4096;
    }
}

pub use target::*;
