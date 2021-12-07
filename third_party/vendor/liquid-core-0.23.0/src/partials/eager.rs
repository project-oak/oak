use std::collections::HashMap;
use std::fmt;
use std::sync;

use crate::error::Error;
use crate::error::Result;
use crate::parser;
use crate::parser::Language;
use crate::runtime;
use crate::runtime::PartialStore;
use crate::runtime::Renderable;

use super::PartialCompiler;
use super::PartialSource;

/// An eagerly-caching compiler for `PartialSource`.
///
/// This would be useful in cases where:
/// - Most partial-templates are used
/// - Of the used partial-templates, they are generally used many times.
///
/// Note: partial-compilation error reporting is deferred to render-time so content can still be
/// generated even when the content is in an intermediate-state.
#[derive(Debug)]
pub struct EagerCompiler<S: PartialSource> {
    source: S,
}

impl<S> EagerCompiler<S>
where
    S: PartialSource,
{
    /// Create an on-demand compiler for `PartialSource`.
    pub fn new(source: S) -> Self {
        EagerCompiler { source }
    }
}

impl<S> EagerCompiler<S>
where
    S: PartialSource + Default,
{
    /// Create an empty compiler for `PartialSource`.
    pub fn empty() -> Self {
        Default::default()
    }
}

impl<S> Default for EagerCompiler<S>
where
    S: PartialSource + Default,
{
    fn default() -> Self {
        Self {
            source: Default::default(),
        }
    }
}

impl<S> ::std::ops::Deref for EagerCompiler<S>
where
    S: PartialSource,
{
    type Target = S;

    fn deref(&self) -> &S {
        &self.source
    }
}

impl<S> ::std::ops::DerefMut for EagerCompiler<S>
where
    S: PartialSource,
{
    fn deref_mut(&mut self) -> &mut S {
        &mut self.source
    }
}

impl<S> PartialCompiler for EagerCompiler<S>
where
    S: PartialSource + Send + Sync + 'static,
{
    fn compile(self, language: sync::Arc<Language>) -> Result<Box<dyn PartialStore + Send + Sync>> {
        let store: HashMap<_, _> = self
            .source
            .names()
            .into_iter()
            .map(|name| {
                let source = self.source.get(name).and_then(|s| {
                    parser::parse(s.as_ref(), &language)
                        .map(runtime::Template::new)
                        .map(|t| {
                            let t: sync::Arc<dyn runtime::Renderable> = sync::Arc::new(t);
                            t
                        })
                });
                (name.to_owned(), source)
            })
            .collect();
        let store = EagerStore { store };
        Ok(Box::new(store))
    }

    fn source(&self) -> &dyn PartialSource {
        &self.source
    }
}

struct EagerStore {
    store: HashMap<String, Result<sync::Arc<dyn runtime::Renderable>>>,
}

impl PartialStore for EagerStore {
    fn contains(&self, name: &str) -> bool {
        self.store.contains_key(name)
    }

    fn names(&self) -> Vec<&str> {
        self.store.keys().map(|s| s.as_str()).collect()
    }

    fn try_get(&self, name: &str) -> Option<sync::Arc<dyn Renderable>> {
        self.store.get(name).and_then(|r| r.clone().ok())
    }

    fn get(&self, name: &str) -> Result<sync::Arc<dyn Renderable>> {
        let result = self.store.get(name).ok_or_else(|| {
            let mut available: Vec<_> = self.names();
            available.sort_unstable();
            let available = itertools::join(available, ", ");
            Error::with_msg("Unknown partial-template")
                .context("requested partial", name.to_owned())
                .context("available partials", available)
        })?;
        result.clone()
    }
}

impl fmt::Debug for EagerStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.names().fmt(f)
    }
}
