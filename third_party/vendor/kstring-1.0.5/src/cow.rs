use std::{borrow::Cow, fmt};

use crate::KString;
use crate::KStringRef;
use crate::KStringRefInner;

type StdString = std::string::String;
type BoxedStr = Box<str>;

/// A reference to a UTF-8 encoded, immutable string.
#[derive(Clone)]
#[repr(transparent)]
pub struct KStringCow<'s> {
    pub(crate) inner: KStringCowInner<'s>,
}

#[derive(Clone, Debug)]
pub(crate) enum KStringCowInner<'s> {
    Borrowed(&'s str),
    Owned(KString),
}

impl<'s> KStringCow<'s> {
    /// Create a new empty `KStringCow`.
    #[inline]
    pub fn new() -> Self {
        Default::default()
    }

    /// Create an owned `KStringCow`.
    #[inline]
    pub fn from_boxed(other: BoxedStr) -> Self {
        Self {
            inner: KStringCowInner::Owned(KString::from_boxed(other)),
        }
    }

    /// Create an owned `KStringCow`.
    #[inline]
    pub fn from_string(other: StdString) -> Self {
        Self {
            inner: KStringCowInner::Owned(KString::from_string(other)),
        }
    }

    /// Create a reference to a borrowed data.
    #[inline]
    pub fn from_ref(other: &'s str) -> Self {
        Self {
            inner: KStringCowInner::Borrowed(other),
        }
    }

    /// Create a reference to a `'static` data.
    #[inline]
    pub fn from_static(other: &'static str) -> Self {
        Self {
            inner: KStringCowInner::Owned(KString::from_static(other)),
        }
    }

    /// Get a reference to the `KString`.
    #[inline]
    pub fn as_ref(&self) -> KStringRef<'_> {
        self.inner.as_ref()
    }

    /// Clone the data into an owned-type.
    #[inline]
    pub fn into_owned(self) -> KString {
        self.inner.into_owned()
    }

    /// Extracts a string slice containing the entire `KStringCow`.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.inner.as_str()
    }

    /// Convert to a mutable string type, cloning the data if necessary.
    #[inline]
    pub fn into_string(self) -> StdString {
        String::from(self.into_boxed_str())
    }

    /// Convert to a mutable string type, cloning the data if necessary.
    #[inline]
    pub fn into_boxed_str(self) -> BoxedStr {
        self.inner.into_boxed_str()
    }

    /// Convert to a Cow str
    #[inline]
    pub fn into_cow_str(self) -> Cow<'s, str> {
        self.inner.into_cow_str()
    }
}

impl<'s> KStringCowInner<'s> {
    #[inline]
    fn as_ref(&self) -> KStringRef<'_> {
        match self {
            Self::Borrowed(s) => KStringRef::from_ref(s),
            Self::Owned(s) => s.as_ref(),
        }
    }

    #[inline]
    fn into_owned(self) -> KString {
        match self {
            Self::Borrowed(s) => KString::from_ref(s),
            Self::Owned(s) => s,
        }
    }

    #[inline]
    fn as_str(&self) -> &str {
        match self {
            Self::Borrowed(s) => s,
            Self::Owned(s) => s.as_str(),
        }
    }

    #[inline]
    fn into_boxed_str(self) -> BoxedStr {
        match self {
            Self::Borrowed(s) => BoxedStr::from(s),
            Self::Owned(s) => s.into_boxed_str(),
        }
    }

    /// Convert to a Cow str
    #[inline]
    fn into_cow_str(self) -> Cow<'s, str> {
        match self {
            Self::Borrowed(s) => Cow::Borrowed(s),
            Self::Owned(s) => s.into_cow_str(),
        }
    }
}

impl<'s> std::ops::Deref for KStringCow<'s> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<'s> Eq for KStringCow<'s> {}

impl<'s> PartialEq<KStringCow<'s>> for KStringCow<'s> {
    #[inline]
    fn eq(&self, other: &KStringCow<'s>) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl<'s> PartialEq<str> for KStringCow<'s> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        PartialEq::eq(self.as_str(), other)
    }
}

impl<'s> PartialEq<&'s str> for KStringCow<'s> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        PartialEq::eq(self.as_str(), *other)
    }
}

impl<'s> PartialEq<String> for KStringCow<'s> {
    #[inline]
    fn eq(&self, other: &StdString) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl<'s> Ord for KStringCow<'s> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<'s> PartialOrd for KStringCow<'s> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl<'s> std::hash::Hash for KStringCow<'s> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<'s> fmt::Debug for KStringCow<'s> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

impl<'s> fmt::Display for KStringCow<'s> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<'s> AsRef<str> for KStringCow<'s> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<'s> AsRef<[u8]> for KStringCow<'s> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<'s> AsRef<std::ffi::OsStr> for KStringCow<'s> {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        (&**self).as_ref()
    }
}

impl<'s> AsRef<std::path::Path> for KStringCow<'s> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self)
    }
}

impl<'s> std::borrow::Borrow<str> for KStringCow<'s> {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<'s> Default for KStringCow<'s> {
    #[inline]
    fn default() -> Self {
        Self::from_static("")
    }
}

impl<'s> From<KString> for KStringCow<'s> {
    #[inline]
    fn from(other: KString) -> Self {
        let inner = KStringCowInner::Owned(other);
        Self { inner }
    }
}

impl<'s> From<&'s KString> for KStringCow<'s> {
    #[inline]
    fn from(other: &'s KString) -> Self {
        let other = other.as_ref();
        other.into()
    }
}

impl<'s> From<KStringRef<'s>> for KStringCow<'s> {
    #[inline]
    fn from(other: KStringRef<'s>) -> Self {
        match other.inner {
            KStringRefInner::Borrowed(s) => Self::from_ref(s),
            KStringRefInner::Singleton(s) => Self::from_static(s),
        }
    }
}

impl<'s> From<&'s KStringRef<'s>> for KStringCow<'s> {
    #[inline]
    fn from(other: &'s KStringRef<'s>) -> Self {
        match other.inner {
            KStringRefInner::Borrowed(s) => Self::from_ref(s),
            KStringRefInner::Singleton(s) => Self::from_static(s),
        }
    }
}

impl<'s> From<StdString> for KStringCow<'s> {
    #[inline]
    fn from(other: StdString) -> Self {
        Self::from_string(other)
    }
}

impl<'s> From<&'s StdString> for KStringCow<'s> {
    #[inline]
    fn from(other: &'s StdString) -> Self {
        Self::from_ref(other.as_str())
    }
}

impl<'s> From<BoxedStr> for KStringCow<'s> {
    #[inline]
    fn from(other: BoxedStr) -> Self {
        // Since the memory is already allocated, don't bother moving it into a FixedString
        Self::from_boxed(other)
    }
}

impl<'s> From<&'s BoxedStr> for KStringCow<'s> {
    #[inline]
    fn from(other: &'s BoxedStr) -> Self {
        Self::from_ref(other)
    }
}

impl<'s> From<&'s str> for KStringCow<'s> {
    #[inline]
    fn from(other: &'s str) -> Self {
        Self::from_ref(other)
    }
}

#[cfg(feature = "serde")]
impl<'s> serde::Serialize for KStringCow<'s> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "serde")]
impl<'de, 's> serde::Deserialize<'de> for KStringCow<'s> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        KString::deserialize(deserializer).map(|s| s.into())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_size() {
        println!("KStringCow: {}", std::mem::size_of::<KStringCow<'static>>());
    }
}
