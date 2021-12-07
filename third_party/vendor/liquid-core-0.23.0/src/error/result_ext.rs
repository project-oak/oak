use std::error;
use std::result;

use super::CloneableError;
use super::Error;
use super::ErrorClone;
use super::Result;

/// `Result` extension methods for adapting third party errors to `Error`.
pub trait ResultLiquidChainExt<T> {
    /// Create an `Error` with `E` as the cause.
    fn chain<S: Into<kstring::KString>>(self, msg: S) -> Result<T>;

    /// Create an `Error` with `E` as the cause.
    fn chain_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString;
}

/// `Result` extension methods for adapting third party errors to `Error`.
pub trait ResultLiquidReplaceExt<T> {
    /// Create an `Error` ignoring `E` as the cause.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::io;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidReplaceExt;
    ///
    /// let error = Err(io::Error::new(io::ErrorKind::NotFound, "Oops"));
    /// let error: Result<i32> = error.lossy_chain("Missing liquid partial");
    /// ```
    fn lossy_chain<S: Into<kstring::KString>>(self, msg: S) -> Result<T>;

    /// Create an `Error` ignoring `E` as the cause.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::io;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidReplaceExt;
    ///
    /// let filename = "foo";
    /// let error = Err(io::Error::new(io::ErrorKind::NotFound, "Oops"));
    /// let error: Result<i32> = error
    ///     .lossy_chain_with(|| format!("Missing liquid partial: {}", filename).into());
    /// ```
    fn lossy_chain_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString;

    /// Create an `Error` ignoring `E` as the cause.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::io;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidReplaceExt;
    ///
    /// let error = Err(io::Error::new(io::ErrorKind::NotFound, "Oops"));
    /// let error: Result<i32> = error.replace("Missing liquid partial");
    /// ```
    fn replace<S: Into<kstring::KString>>(self, msg: S) -> Result<T>;

    /// Create an `Error` ignoring `E` as the cause.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::io;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidReplaceExt;
    ///
    /// let filename = "foo";
    /// let error = Err(io::Error::new(io::ErrorKind::NotFound, "Oops"));
    /// let error: Result<i32> = error
    ///     .replace_with(|| format!("Missing liquid partial: {}", filename).into());
    /// ```
    fn replace_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString;
}

impl<T, E> ResultLiquidChainExt<T> for result::Result<T, E>
where
    E: ErrorClone,
{
    fn chain<S: Into<kstring::KString>>(self, msg: S) -> Result<T> {
        self.map_err(|err| Error::with_msg(msg).cause(err))
    }

    fn chain_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString,
    {
        self.map_err(|err| Error::with_msg(msg()).cause(err))
    }
}

impl<T, E> ResultLiquidReplaceExt<T> for result::Result<T, E>
where
    E: error::Error + Send + Sync + 'static,
{
    fn lossy_chain<S: Into<kstring::KString>>(self, msg: S) -> Result<T> {
        self.map_err(|err| Error::with_msg(msg).cause(CloneableError::new(err)))
    }

    fn lossy_chain_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString,
    {
        self.map_err(|err| Error::with_msg(msg()).cause(CloneableError::new(err)))
    }

    fn replace<S: Into<kstring::KString>>(self, msg: S) -> Result<T> {
        self.map_err(|_| Error::with_msg(msg))
    }

    fn replace_with<F>(self, msg: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString,
    {
        self.map_err(|_| Error::with_msg(msg()))
    }
}

/// Add context to a `crate::error::Error`.
pub trait ResultLiquidExt<T>
where
    Self: ::std::marker::Sized,
{
    /// Add a new stack frame to the `crate::error::Error`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use liquid_core::error::Error;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidExt;
    ///
    /// let error: Result<i32> = Err(Error::with_msg("Oops"));
    /// let error = error.trace("Within forloop");
    /// ```
    fn trace<S>(self, trace: S) -> Result<T>
    where
        S: Into<kstring::KString>;

    /// Add a new stack frame to the `crate::error::Error`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use liquid_core::error::Error;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidExt;
    ///
    /// let for_var = "foo";
    /// let error: Result<i32> = Err(Error::with_msg("Oops"));
    /// let error = error.trace_with(|| format!("Within forloop with {}", for_var).into());
    /// ```
    fn trace_with<F>(self, trace: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString;

    /// Add state the current stack frame.
    ///
    /// # Example
    ///
    /// ```rust
    /// use liquid_core::error::Error;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidExt;
    ///
    /// let for_var = "foo";
    /// let error: Result<i32> = Err(Error::with_msg("Oops"));
    /// let error = error
    ///     .context_key("foo")
    ///     .value("10");
    /// let error = error
    ///     .context_key("foo")
    ///     .value_with(|| format!("{}", for_var).into());
    /// ```
    #[must_use]
    fn context_key<S>(self, key: S) -> Key<T>
    where
        S: Into<kstring::KString>;

    /// Add state the current stack frame.
    ///
    /// # Example
    ///
    /// ```rust
    /// use liquid_core::error::Error;
    /// use liquid_core::error::Result;
    /// use liquid_core::error::ResultLiquidExt;
    ///
    /// let for_var = "foo";
    /// let error: Result<i32> = Err(Error::with_msg("Oops"));
    /// let error = error
    ///     .context_key_with(|| format!("{}", 10).into())
    ///     .value("10");
    /// let error = error
    ///     .context_key_with(|| format!("{}", 10).into())
    ///     .value_with(|| format!("{}", for_var).into());
    /// ```
    #[must_use]
    fn context_key_with<F>(self, key: F) -> FnKey<T, F>
    where
        F: FnOnce() -> kstring::KString;
}

impl<T> ResultLiquidExt<T> for Result<T> {
    fn trace<S>(self, trace: S) -> Result<T>
    where
        S: Into<kstring::KString>,
    {
        self.map_err(|err| err.trace(trace))
    }

    fn trace_with<F>(self, trace: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString,
    {
        self.map_err(|err| err.trace(trace()))
    }

    fn context_key<S>(self, key: S) -> Key<T>
    where
        S: Into<kstring::KString>,
    {
        Key::new(self, key)
    }

    fn context_key_with<F>(self, key: F) -> FnKey<T, F>
    where
        F: FnOnce() -> kstring::KString,
    {
        FnKey::new(self, key)
    }
}

/// Partially constructed context (missing value) for `Result<T>`.
#[allow(missing_debug_implementations)]
pub struct Key<T> {
    builder: Result<T>,
    key: kstring::KString,
}

impl<T> Key<T> {
    /// Save off a key for a context that will be added to `builder`.
    #[must_use]
    pub fn new<S>(builder: Result<T>, key: S) -> Self
    where
        S: Into<kstring::KString>,
    {
        Self {
            builder,
            key: key.into(),
        }
    }

    /// Finish creating context and add it to `Result<T>`.
    pub fn value<S>(self, value: S) -> Result<T>
    where
        S: Into<kstring::KString>,
    {
        let builder = self.builder;
        let key = self.key;
        builder.map_err(|err| err.context(key, value.into()))
    }

    /// Finish creating context and add it to `Result<T>`.
    pub fn value_with<F>(self, value: F) -> Result<T>
    where
        F: FnOnce() -> kstring::KString,
    {
        let builder = self.builder;
        let key = self.key;
        builder.map_err(|err| err.context(key, value()))
    }
}

/// Partially constructed context (missing value) for `Result<T>`.
#[allow(missing_debug_implementations)]
pub struct FnKey<T, F>
where
    F: FnOnce() -> kstring::KString,
{
    builder: Result<T>,
    key: F,
}

impl<T, F> FnKey<T, F>
where
    F: FnOnce() -> kstring::KString,
{
    /// Save off a key for a context that will be added to `builder`.
    #[must_use]
    pub fn new(builder: Result<T>, key: F) -> Self {
        Self { builder, key }
    }

    /// Finish creating context and add it to `Result<T>`.
    pub fn value<S>(self, value: S) -> Result<T>
    where
        S: Into<kstring::KString>,
    {
        let builder = self.builder;
        let key = self.key;
        builder.map_err(|err| err.context((key)(), value.into()))
    }

    /// Finish creating context and add it to `Result<T>`.
    pub fn value_with<V>(self, value: V) -> Result<T>
    where
        V: FnOnce() -> kstring::KString,
    {
        let builder = self.builder;
        let key = self.key;
        builder.map_err(|err| err.context((key)(), value()))
    }
}
