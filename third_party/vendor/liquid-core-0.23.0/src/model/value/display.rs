use std::fmt;

/// Abstract the lifetime of a `Display`.
#[allow(missing_debug_implementations)]
pub enum DisplayCow<'a> {
    /// A boxed `Display`
    Owned(Box<dyn fmt::Display + 'a>),
    /// A borrowed `Display`
    Borrowed(&'a dyn fmt::Display),
}

impl<'a> DisplayCow<'a> {
    fn as_ref(&self) -> &dyn fmt::Display {
        match self {
            DisplayCow::Owned(o) => o.as_ref(),
            DisplayCow::Borrowed(b) => b,
        }
    }
}

impl<'a> fmt::Display for DisplayCow<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

pub(crate) struct StrDisplay {
    pub(crate) s: &'static str,
}

impl fmt::Display for StrDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.s)
    }
}
