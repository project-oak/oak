use std::borrow;
use std::fmt;
use std::sync;

use crate::error::Error;
use crate::error::Result;
use crate::parser::Language;
use crate::runtime::PartialStore;

mod eager;
mod inmemory;
mod lazy;
mod ondemand;

pub use self::eager::*;
pub use self::inmemory::*;
pub use self::lazy::*;
pub use self::ondemand::*;

/// Compile a `PartialSource` into a `PartialStore` of `Renderable`s.
///
/// This trait is intended to allow a variety of implementation/policies to fit your needs,
/// including:
/// - Compile partials eagerly or lazily.
/// - Report compile errors eagerly or lazily.
/// - Whether to cache the results or not.
pub trait PartialCompiler {
    /// Convert a `PartialSource` into a `PartialStore`.
    fn compile(self, language: sync::Arc<Language>) -> Result<Box<dyn PartialStore + Send + Sync>>;

    /// Access underlying `PartialSource`
    fn source(&self) -> &dyn PartialSource;
}

/// Partial-template source repository.
pub trait PartialSource: fmt::Debug {
    /// Check if partial-template exists.
    fn contains(&self, name: &str) -> bool;

    /// Enumerate all partial-templates.
    fn names(&self) -> Vec<&str>;

    /// Access a partial-template.
    fn try_get<'a>(&'a self, name: &str) -> Option<borrow::Cow<'a, str>>;

    /// Access a partial-template
    fn get<'a>(&'a self, name: &str) -> Result<borrow::Cow<'a, str>> {
        self.try_get(name).ok_or_else(|| {
            let mut available: Vec<_> = self.names();
            available.sort_unstable();
            let available = itertools::join(available, ", ");
            Error::with_msg("Unknown partial-template")
                .context("requested partial", name.to_owned())
                .context("available partials", available)
        })
    }
}
