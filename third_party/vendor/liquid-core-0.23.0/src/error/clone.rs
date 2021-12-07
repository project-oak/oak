use std::error;
use std::fmt;

/// An error that can be cloned.
pub trait ErrorClone: error::Error + Send + Sync + 'static {
    /// Clone the error.
    fn clone_box(&self) -> Box<dyn ErrorClone>;
}

impl<E> ErrorClone for E
where
    E: error::Error + Clone + Send + Sync + 'static,
{
    fn clone_box(&self) -> Box<dyn ErrorClone> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn ErrorClone> {
    fn clone(&self) -> Box<dyn ErrorClone> {
        self.clone_box()
    }
}

/// A lossy way to have any error be clonable.
#[derive(Debug, Clone)]
pub struct CloneableError {
    error: String,
}

impl CloneableError {
    /// Lossily make any error cloneable.
    pub fn new<E>(error: E) -> Self
    where
        E: error::Error + Send + Sync + 'static,
    {
        Self {
            error: error.to_string(),
        }
    }
}

impl fmt::Display for CloneableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.error)
    }
}

impl error::Error for CloneableError {
    fn description(&self) -> &str {
        self.error.as_str()
    }

    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}
