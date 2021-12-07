//! The Liquid templating language for Rust
//!
//! __[liquidmarkup.org](http://liquidmarkup.org/)__
//!
//! ```toml
//! [dependencies]
//! liquid = "0.20"
//! ```
//!
//! ## Example
//! ```rust
//! let template = liquid::ParserBuilder::with_stdlib()
//!     .build().unwrap()
//!     .parse("Liquid! {{num | minus: 2}}").unwrap();
//!
//! let mut globals = liquid::object!({
//!     "num": 4f64
//! });
//!
//! let output = template.render(&globals).unwrap();
//! assert_eq!(output, "Liquid! 2".to_string());
//! ```

mod parser;
mod template;

pub mod reflection;

pub use liquid_core::partials;
/// Liquid data model.
pub mod model {
    pub use liquid_core::array;
    pub use liquid_core::model::*;
    pub use liquid_core::object;
    pub use liquid_core::scalar;
    pub use liquid_core::value;
}

pub use crate::parser::*;
pub use crate::template::*;
pub use liquid_core::model::{_ObjectView as ObjectView, _ValueView as ValueView};
pub use liquid_core::object;
pub use liquid_core::to_object;
pub use liquid_core::Error;
pub use liquid_core::Object;
#[doc(hidden)]
pub use liquid_derive::{ObjectView, ValueView};

#[macro_use]
extern crate doc_comment;
doc_comment! {
    include_str!("../README.md")
}
