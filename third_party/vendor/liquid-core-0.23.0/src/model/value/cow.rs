use std::fmt;

use kstring::KStringCow;

use super::DisplayCow;
use super::State;
use super::Value;
use super::{ValueView, ValueViewCmp};
use crate::model::array::{Array, ArrayView};
use crate::model::object::{Object, ObjectView};
use crate::model::scalar::{Scalar, ScalarCow};

/// Abstract the lifetime of a `Value`.
#[derive(Clone, Debug)]
pub enum ValueCow<'s> {
    /// A boxed `Value`
    Owned(Value),
    /// A borrowed `Value`
    Borrowed(&'s dyn ValueView),
}

impl<'s> ValueCow<'s> {
    /// Extracts the owned data.
    ///
    /// Clones the data if it is not already owned.
    pub fn into_owned(self) -> Value {
        match self {
            ValueCow::Owned(x) => x,
            ValueCow::Borrowed(x) => x.to_value(),
        }
    }

    /// Performs the conversion.
    pub fn as_view(&self) -> &dyn ValueView {
        match self {
            ValueCow::Owned(o) => o.as_view(),
            ValueCow::Borrowed(b) => *b,
        }
    }
}

impl<'s> ValueView for ValueCow<'s> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        self.as_view().render()
    }
    fn source(&self) -> DisplayCow<'_> {
        self.as_view().source()
    }
    fn type_name(&self) -> &'static str {
        self.as_view().type_name()
    }
    fn query_state(&self, state: State) -> bool {
        self.as_view().query_state(state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.as_view().to_kstr()
    }
    fn to_value(&self) -> Value {
        self.as_view().to_value()
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        self.as_view().as_scalar()
    }

    fn as_array(&self) -> Option<&dyn ArrayView> {
        self.as_view().as_array()
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        self.as_view().as_object()
    }

    fn as_state(&self) -> Option<State> {
        self.as_view().as_state()
    }

    fn is_nil(&self) -> bool {
        self.as_view().is_nil()
    }
}

impl From<Value> for ValueCow<'static> {
    fn from(other: Value) -> Self {
        ValueCow::Owned(other)
    }
}

impl<'s> From<&'s Value> for ValueCow<'s> {
    fn from(other: &'s Value) -> Self {
        ValueCow::Borrowed(other.as_view())
    }
}

impl From<Scalar> for ValueCow<'static> {
    fn from(other: Scalar) -> Self {
        ValueCow::Owned(Value::Scalar(other))
    }
}

impl From<Array> for ValueCow<'static> {
    fn from(other: Array) -> Self {
        ValueCow::Owned(Value::Array(other))
    }
}

impl From<Object> for ValueCow<'static> {
    fn from(other: Object) -> Self {
        ValueCow::Owned(Value::Object(other))
    }
}

impl From<State> for ValueCow<'static> {
    fn from(other: State) -> Self {
        ValueCow::Owned(Value::State(other))
    }
}

impl<'v> Default for ValueCow<'v> {
    fn default() -> Self {
        ValueCow::Owned(Value::default())
    }
}

impl<'v> PartialEq<ValueCow<'v>> for ValueCow<'v> {
    fn eq(&self, other: &Self) -> bool {
        super::value_eq(self.as_view(), other.as_view())
    }
}

impl<'v> PartialEq<ValueViewCmp<'v>> for ValueCow<'v> {
    fn eq(&self, other: &ValueViewCmp<'v>) -> bool {
        ValueViewCmp::new(self.as_view()) == *other
    }
}

impl<'v> PartialEq<Value> for ValueCow<'v> {
    fn eq(&self, other: &Value) -> bool {
        super::value_eq(self.as_view(), other.as_view())
    }
}

impl<'v> PartialEq<i64> for ValueCow<'v> {
    fn eq(&self, other: &i64) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<f64> for ValueCow<'v> {
    fn eq(&self, other: &f64) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<bool> for ValueCow<'v> {
    fn eq(&self, other: &bool) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<crate::model::scalar::DateTime> for ValueCow<'v> {
    fn eq(&self, other: &crate::model::scalar::DateTime) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<crate::model::scalar::Date> for ValueCow<'v> {
    fn eq(&self, other: &crate::model::scalar::Date) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<str> for ValueCow<'v> {
    fn eq(&self, other: &str) -> bool {
        let other = KStringCow::from_ref(other);
        super::value_eq(self.as_view(), &other)
    }
}

impl<'v> PartialEq<&'v str> for ValueCow<'v> {
    fn eq(&self, other: &&str) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<String> for ValueCow<'v> {
    fn eq(&self, other: &String) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<kstring::KString> for ValueCow<'v> {
    fn eq(&self, other: &kstring::KString) -> bool {
        super::value_eq(self.as_view(), &other.as_ref())
    }
}

impl<'v> PartialEq<kstring::KStringRef<'v>> for ValueCow<'v> {
    fn eq(&self, other: &kstring::KStringRef<'v>) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'v> PartialEq<kstring::KStringCow<'v>> for ValueCow<'v> {
    fn eq(&self, other: &kstring::KStringCow<'v>) -> bool {
        super::value_eq(self.as_view(), other)
    }
}
