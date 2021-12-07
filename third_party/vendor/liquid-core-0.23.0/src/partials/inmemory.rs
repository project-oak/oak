use std::borrow;
use std::collections::HashMap;

use super::PartialSource;

/// In-memory collection of partial-template source code.
#[derive(Debug, Default, Clone)]
pub struct InMemorySource {
    data: HashMap<String, String>,
}

impl InMemorySource {
    /// Create an in-memory repository to store partial-template source.
    pub fn new() -> Self {
        Default::default()
    }

    /// Add a partial-template's source.
    pub fn add<N, S>(&mut self, name: N, source: S) -> bool
    where
        N: Into<String>,
        S: Into<String>,
    {
        self.data.insert(name.into(), source.into()).is_some()
    }
}

impl PartialSource for InMemorySource {
    fn contains(&self, name: &str) -> bool {
        self.data.contains_key(name)
    }

    fn names(&self) -> Vec<&str> {
        self.data.keys().map(|s| s.as_str()).collect()
    }

    fn try_get<'a>(&'a self, name: &str) -> Option<borrow::Cow<'a, str>> {
        self.data.get(name).map(|s| s.as_str().into())
    }
}
