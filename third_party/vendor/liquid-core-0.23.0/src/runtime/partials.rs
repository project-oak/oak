use std::fmt;
use std::sync;

use crate::error::Result;

use super::Renderable;

/// Available partial-templates for including.
pub trait PartialStore: fmt::Debug {
    /// Check if partial-template exists.
    fn contains(&self, name: &str) -> bool;

    /// Enumerate all partial-templates.
    fn names(&self) -> Vec<&str>;

    /// Access a partial-template.
    fn try_get(&self, name: &str) -> Option<sync::Arc<dyn Renderable>>;

    /// Access a .partial-template
    fn get(&self, name: &str) -> Result<sync::Arc<dyn Renderable>>;
}
