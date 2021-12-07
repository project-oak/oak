//! Liquid data model.

#![warn(missing_docs)]
#![warn(missing_debug_implementations)]
#![warn(unused_extern_crates)]

mod array;
mod find;
mod object;
mod scalar;
mod value;

mod ser;

pub use array::*;
pub use find::*;
pub use object::*;
pub use scalar::*;
pub use value::*;

#[cfg(feature = "derive")]
#[doc(hidden)]
pub use liquid_derive::CoreObjectView as ObjectView;
#[cfg(feature = "derive")]
#[doc(hidden)]
pub use liquid_derive::CoreValueView as ValueView;
#[doc(hidden)]
pub use object::ObjectView as _ObjectView;
#[doc(hidden)]
pub use value::ValueView as _ValueView;
