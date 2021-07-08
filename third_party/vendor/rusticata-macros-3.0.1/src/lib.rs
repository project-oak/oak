//! # Rusticata-macros
//!
//! Helper macros for the [rusticata](https://github.com/rusticata) project.
//!
//! This crate contains some additions to [nom](https://github.com/Geal/nom).
//!
//! For example, the `error_if!` macro allows to test a condition and return an error from the parser if the condition
//! fails:
//!
//! ```rust
//! # extern crate rusticata_macros;
//! # extern crate nom;
//! # use nom::{do_parse, take, IResult};
//! # use nom::error::ErrorKind;
//! # use nom::number::streaming::be_u8;
//! use rusticata_macros::error_if;
//! # fn parser(s:&[u8]) {
//! let r : IResult<&[u8],()> = do_parse!(
//!     s,
//!     l: be_u8 >>
//!     error_if!(l < 4, ErrorKind::Verify) >>
//!     data: take!(l - 4) >>
//!     (())
//!     );
//! # }
//! ```
//!
//! See the documentation for more details and examples.

#![deny(
    missing_docs,
    unsafe_code,
    unstable_features,
    unused_import_braces,
    unused_qualifications
)]

#[macro_use]
extern crate nom;

pub mod combinator;

pub use macros::*;
#[macro_use]
pub mod macros;

pub mod debug;
mod traits;
pub use traits::*;
