use std::{borrow::Cow, fmt};

use crate::inline::*;
use crate::KStringCow;
use crate::KStringRef;

pub(crate) type StdString = std::string::String;
type BoxedStr = Box<str>;
#[cfg(feature = "arc")]
pub(crate) type OwnedStr = std::sync::Arc<str>;
#[cfg(not(feature = "arc"))]
pub(crate) type OwnedStr = Box<str>;

/// A UTF-8 encoded, immutable string.
#[derive(Clone)]
#[repr(transparent)]
pub struct KString {
    pub(crate) inner: KStringInner,
}

#[derive(Debug)]
pub(crate) enum KStringInner {
    Singleton(&'static str),
    Inline(InlineString),
    Owned(OwnedStr),
}

impl KString {
    /// Create a new empty `KString`.
    #[inline]
    pub fn new() -> Self {
        Default::default()
    }

    /// Create an owned `KString`.
    #[inline]
    pub fn from_boxed(other: BoxedStr) -> Self {
        Self {
            inner: KStringInner::Owned(OwnedStr::from(other)),
        }
    }

    /// Create an owned `KString`.
    #[inline]
    pub fn from_string(other: StdString) -> Self {
        let inner = if (0..=CAPACITY).contains(&other.len()) {
            KStringInner::Inline(InlineString::new(other.as_str()))
        } else {
            KStringInner::Owned(OwnedStr::from(other.into_boxed_str()))
        };
        Self { inner }
    }

    /// Create an owned `KString` optimally from a reference.
    #[inline]
    pub fn from_ref(other: &str) -> Self {
        let inner = if (0..=CAPACITY).contains(&other.len()) {
            KStringInner::Inline(InlineString::new(other))
        } else {
            KStringInner::Owned(OwnedStr::from(other))
        };
        Self { inner }
    }

    /// Create a reference to a `'static` data.
    #[inline]
    pub fn from_static(other: &'static str) -> Self {
        Self {
            inner: KStringInner::Singleton(other),
        }
    }

    /// Get a reference to the `KString`.
    #[inline]
    pub fn as_ref(&self) -> KStringRef<'_> {
        self.inner.as_ref()
    }

    /// Extracts a string slice containing the entire `KString`.
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
    pub fn into_cow_str(self) -> Cow<'static, str> {
        self.inner.into_cow_str()
    }
}

impl KStringInner {
    #[inline]
    fn as_ref(&self) -> KStringRef<'_> {
        match self {
            Self::Singleton(s) => KStringRef::from_static(s),
            Self::Inline(s) => KStringRef::from_ref(s.as_str()),
            Self::Owned(s) => KStringRef::from_ref(s),
        }
    }

    #[inline]
    fn as_str(&self) -> &str {
        match self {
            Self::Singleton(s) => s,
            Self::Inline(s) => s.as_str(),
            Self::Owned(s) => &s,
        }
    }

    #[inline]
    fn into_boxed_str(self) -> BoxedStr {
        match self {
            Self::Singleton(s) => BoxedStr::from(s),
            Self::Inline(s) => s.to_boxed_str(),
            Self::Owned(s) => BoxedStr::from(s.as_ref()),
        }
    }

    /// Convert to a Cow str
    #[inline]
    fn into_cow_str(self) -> Cow<'static, str> {
        match self {
            Self::Singleton(s) => Cow::Borrowed(s),
            Self::Inline(s) => Cow::Owned(s.to_boxed_str().into()),
            Self::Owned(s) => Cow::Owned(s.as_ref().into()),
        }
    }
}

// Explicit to avoid inlining which cuts clone times in half.
//
// An automatically derived `clone()` has 10ns overhead while the explicit `Deref`/`as_str` has
// none of that.  Being explicit and removing the `#[inline]` attribute dropped the overhead to
// 5ns.
//
// My only guess is that the `clone()` calls we delegate to are just that much bigger than
// `as_str()` that, when combined with a jump table, is blowing the icache, slowing things down.
impl Clone for KStringInner {
    fn clone(&self) -> Self {
        match self {
            Self::Singleton(s) => Self::Singleton(s),
            Self::Inline(s) => Self::Inline(*s),
            Self::Owned(s) => Self::Owned(s.clone()),
        }
    }
}

impl std::ops::Deref for KString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl Eq for KString {}

impl<'s> PartialEq<KString> for KString {
    #[inline]
    fn eq(&self, other: &KString) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl<'s> PartialEq<str> for KString {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        PartialEq::eq(self.as_str(), other)
    }
}

impl<'s> PartialEq<&'s str> for KString {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        PartialEq::eq(self.as_str(), *other)
    }
}

impl<'s> PartialEq<String> for KString {
    #[inline]
    fn eq(&self, other: &StdString) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl Ord for KString {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for KString {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl std::hash::Hash for KString {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl fmt::Debug for KString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

impl fmt::Display for KString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl AsRef<str> for KString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for KString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<std::ffi::OsStr> for KString {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        (&**self).as_ref()
    }
}

impl AsRef<std::path::Path> for KString {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self)
    }
}

impl std::borrow::Borrow<str> for KString {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Default for KString {
    #[inline]
    fn default() -> Self {
        Self::from_static("")
    }
}

impl<'s> From<KStringRef<'s>> for KString {
    #[inline]
    fn from(other: KStringRef<'s>) -> Self {
        other.to_owned()
    }
}

impl<'s> From<&'s KStringRef<'s>> for KString {
    #[inline]
    fn from(other: &'s KStringRef<'s>) -> Self {
        other.to_owned()
    }
}

impl<'s> From<KStringCow<'s>> for KString {
    #[inline]
    fn from(other: KStringCow<'s>) -> Self {
        other.into_owned()
    }
}

impl<'s> From<&'s KStringCow<'s>> for KString {
    #[inline]
    fn from(other: &'s KStringCow<'s>) -> Self {
        other.clone().into_owned()
    }
}

impl From<StdString> for KString {
    #[inline]
    fn from(other: StdString) -> Self {
        Self::from_string(other)
    }
}

impl<'s> From<&'s StdString> for KString {
    #[inline]
    fn from(other: &'s StdString) -> Self {
        Self::from_ref(other)
    }
}

impl From<BoxedStr> for KString {
    #[inline]
    fn from(other: BoxedStr) -> Self {
        Self::from_boxed(other)
    }
}

impl<'s> From<&'s BoxedStr> for KString {
    #[inline]
    fn from(other: &'s BoxedStr) -> Self {
        Self::from_ref(other)
    }
}

impl From<&'static str> for KString {
    #[inline]
    fn from(other: &'static str) -> Self {
        Self::from_static(other)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for KString {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for KString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_string(StringVisitor)
    }
}

#[cfg(feature = "serde")]
struct StringVisitor;

#[cfg(feature = "serde")]
impl<'de> serde::de::Visitor<'de> for StringVisitor {
    type Value = KString;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(KString::from_ref(v))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(KString::from_string(v))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        match std::str::from_utf8(v) {
            Ok(s) => Ok(KString::from_ref(s)),
            Err(_) => Err(serde::de::Error::invalid_value(
                serde::de::Unexpected::Bytes(v),
                &self,
            )),
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        match String::from_utf8(v) {
            Ok(s) => Ok(KString::from_string(s)),
            Err(e) => Err(serde::de::Error::invalid_value(
                serde::de::Unexpected::Bytes(&e.into_bytes()),
                &self,
            )),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_size() {
        println!("KString: {}", std::mem::size_of::<KString>());
    }
}
