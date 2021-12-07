#![allow(clippy::eq_op)]

use std::cmp::Ordering;
use std::fmt;

use kstring::KStringCow;

use super::DisplayCow;
use super::State;
use super::{ValueView, ValueViewCmp};
use crate::model::array::{Array, ArrayView};
use crate::model::object::{Object, ObjectView};
use crate::model::scalar::{Scalar, ScalarCow};

/// An enum to represent different value types
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum Value {
    /// A scalar value.
    Scalar(Scalar),
    /// A sequence of `Value`s.
    Array(Array),
    /// A sequence of key/`Value` pairs.
    Object(Object),
    /// Query symbol.
    State(State),
    /// Nothing.
    Nil,
}

impl Value {
    /// Create as a `Scalar`.
    pub fn scalar<T: Into<Scalar>>(value: T) -> Self {
        Value::Scalar(ScalarCow::new(value))
    }

    /// Create as an `Array`.
    pub fn array<I: IntoIterator<Item = Value>>(iter: I) -> Value {
        let v: Array = iter.into_iter().collect();
        Value::Array(v)
    }

    /// Performs the conversion.
    pub fn as_view(&self) -> &dyn ValueView {
        match &self {
            Value::Scalar(ref x) => x,
            Value::Object(ref x) => x,
            Value::Array(ref x) => x,
            Value::State(ref x) => x,
            Value::Nil => self,
        }
    }

    /// Extracts the scalar value if it is a scalar.
    pub fn into_scalar(self) -> Option<Scalar> {
        match self {
            Value::Scalar(s) => Some(s),
            _ => None,
        }
    }

    /// Extracts the array value if it is an array.
    pub fn into_array(self) -> Option<Array> {
        match self {
            Value::Array(s) => Some(s),
            _ => None,
        }
    }

    /// Extracts the array value as mutable if it is a object.
    pub fn as_array_mut(&mut self) -> Option<&mut Array> {
        match *self {
            Value::Array(ref mut s) => Some(s),
            _ => None,
        }
    }

    /// Extracts the object value if it is a object.
    pub fn into_object(self) -> Option<Object> {
        match self {
            Value::Object(s) => Some(s),
            _ => None,
        }
    }

    /// Extracts the object value as mutable if it is a object.
    pub fn as_object_mut(&mut self) -> Option<&mut Object> {
        match *self {
            Value::Object(ref mut s) => Some(s),
            _ => None,
        }
    }

    /// Extracts the state if it is one
    pub fn into_state(self) -> Option<State> {
        match self {
            Value::State(s) => Some(s),
            _ => None,
        }
    }
}

impl ValueView for Value {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        match *self {
            Value::Scalar(ref x) => x.render(),
            Value::Array(ref x) => x.render(),
            Value::Object(ref x) => x.render(),
            Value::State(ref x) => x.render(),
            Value::Nil => DisplayCow::Borrowed(&""),
        }
    }
    fn source(&self) -> DisplayCow<'_> {
        match *self {
            Value::Scalar(ref x) => x.source(),
            Value::Array(ref x) => x.source(),
            Value::Object(ref x) => x.source(),
            Value::State(ref x) => x.source(),
            Value::Nil => DisplayCow::Owned(Box::new(super::StrDisplay {
                s: self.type_name(),
            })),
        }
    }
    fn type_name(&self) -> &'static str {
        match *self {
            Value::Scalar(ref x) => x.type_name(),
            Value::Array(ref x) => x.type_name(),
            Value::Object(ref x) => x.type_name(),
            Value::State(ref x) => x.type_name(),
            Value::Nil => "nil",
        }
    }
    fn query_state(&self, state: State) -> bool {
        match *self {
            Value::Scalar(ref x) => x.query_state(state),
            Value::Array(ref x) => x.query_state(state),
            Value::Object(ref x) => x.query_state(state),
            Value::State(ref x) => x.query_state(state),
            Value::Nil => match state {
                State::Truthy => false,
                State::DefaultValue => true,
                State::Empty => true,
                State::Blank => true,
            },
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        match *self {
            Value::Scalar(ref x) => x.to_kstr(),
            Value::Array(ref x) => x.to_kstr(),
            Value::Object(ref x) => x.to_kstr(),
            Value::State(ref x) => x.to_kstr(),
            Value::Nil => KStringCow::from_static(""),
        }
    }
    fn to_value(&self) -> Value {
        match self {
            Value::Scalar(ref x) => {
                let x = x.clone();
                let x = x.into_owned();
                Value::Scalar(x)
            }
            Value::Array(ref x) => Value::Array(x.clone()),
            Value::Object(ref x) => Value::Object(x.clone()),
            Value::State(ref x) => Value::State(*x),
            Value::Nil => Value::Nil,
        }
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        match self {
            Value::Scalar(s) => Some(s.as_ref()),
            _ => None,
        }
    }
    fn as_array(&self) -> Option<&dyn ArrayView> {
        match self {
            Value::Array(ref s) => Some(s),
            _ => None,
        }
    }
    fn as_object(&self) -> Option<&dyn ObjectView> {
        match self {
            Value::Object(ref s) => Some(s),
            _ => None,
        }
    }
    fn as_state(&self) -> Option<State> {
        match self {
            Value::State(s) => Some(*s),
            _ => None,
        }
    }
    fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }
}

impl From<Scalar> for Value {
    fn from(other: Scalar) -> Self {
        Value::Scalar(other)
    }
}

impl From<Array> for Value {
    fn from(other: Array) -> Self {
        Value::Array(other)
    }
}

impl From<Object> for Value {
    fn from(other: Object) -> Self {
        Value::Object(other)
    }
}

impl From<State> for Value {
    fn from(other: State) -> Self {
        Value::State(other)
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::Nil
    }
}

impl PartialEq<Value> for Value {
    fn eq(&self, other: &Self) -> bool {
        super::value_eq(self.as_view(), other.as_view())
    }
}

impl<'v> PartialEq<ValueViewCmp<'v>> for Value {
    fn eq(&self, other: &ValueViewCmp<'v>) -> bool {
        ValueViewCmp::new(self.as_view()) == *other
    }
}

impl PartialEq<i64> for Value {
    fn eq(&self, other: &i64) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<f64> for Value {
    fn eq(&self, other: &f64) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<crate::model::scalar::DateTime> for Value {
    fn eq(&self, other: &crate::model::scalar::DateTime) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<crate::model::scalar::Date> for Value {
    fn eq(&self, other: &crate::model::scalar::Date) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        let other = KStringCow::from_ref(other);
        super::value_eq(self.as_view(), &other)
    }
}

impl<'s> PartialEq<&'s str> for Value {
    fn eq(&self, other: &&str) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'s> PartialEq<String> for Value {
    fn eq(&self, other: &String) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl PartialEq<kstring::KString> for Value {
    fn eq(&self, other: &kstring::KString) -> bool {
        super::value_eq(self.as_view(), &other.as_ref())
    }
}

impl<'s> PartialEq<kstring::KStringRef<'s>> for Value {
    fn eq(&self, other: &kstring::KStringRef<'s>) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl<'s> PartialEq<kstring::KStringCow<'s>> for Value {
    fn eq(&self, other: &kstring::KStringCow<'s>) -> bool {
        super::value_eq(self.as_view(), other)
    }
}

impl Eq for Value {}

impl PartialOrd<Value> for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        super::value_cmp(self.as_view(), other)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_to_string_scalar() {
        let val = Value::scalar(42f64);
        assert_eq!(&val.render().to_string(), "42");
        assert_eq!(&val.to_kstr(), "42");
    }

    #[test]
    fn test_to_string_array() {
        let val = Value::Array(vec![
            Value::scalar(3f64),
            Value::scalar("test"),
            Value::scalar(5.3),
        ]);
        assert_eq!(&val.render().to_string(), "3test5.3");
        assert_eq!(&val.to_kstr(), "3test5.3");
    }

    // TODO make a test for object, remember values are in arbitrary orders in HashMaps

    #[test]
    fn test_to_string_nil() {
        assert_eq!(&Value::Nil.render().to_string(), "");
        assert_eq!(&Value::Nil.to_kstr(), "");
    }

    #[test]
    fn scalar_equality() {
        assert_eq!(Value::scalar("alpha"), Value::scalar("alpha"));
        assert_eq!(Value::scalar(""), Value::scalar(""));
        assert!(Value::scalar("alpha") != Value::scalar("beta"));
        assert!(Value::scalar("beta") != Value::scalar("alpha"));
    }

    #[test]
    fn scalars_have_ruby_truthiness() {
        // all strings in ruby are true
        assert_eq!(Value::scalar(true), Value::scalar("All strings are truthy"));
        assert_eq!(Value::scalar(true), Value::scalar(""));
        assert!(Value::scalar("").query_state(State::Truthy));

        assert_eq!(Value::scalar(true), Value::scalar(true));
        assert!(Value::scalar(true) != Value::scalar(false));
    }

    #[test]
    fn array_equality() {
        let a = Value::Array(vec![Value::scalar("one"), Value::scalar("two")]);
        let b = Value::Array(vec![Value::scalar("alpha"), Value::scalar("beta")]);

        assert_eq!(a, a);
        assert!(a != b);
        assert!(b != a);
    }

    #[test]
    fn arrays_have_ruby_truthiness() {
        assert_eq!(Value::scalar(true), Value::Array(Vec::new()));
        assert!(Value::Array(Vec::new()).query_state(State::Truthy));
    }

    #[test]
    fn object_equality() {
        let a: Object = [
            ("alpha".into(), Value::scalar("1")),
            ("beta".into(), Value::scalar(2f64)),
        ]
        .iter()
        .cloned()
        .collect();
        let a = Value::Object(a);

        let b: Object = [
            ("alpha".into(), Value::scalar("1")),
            ("beta".into(), Value::scalar(2f64)),
            ("gamma".into(), Value::Array(vec![])),
        ]
        .iter()
        .cloned()
        .collect();
        let b = Value::Object(b);

        assert_eq!(a, a);
        assert!(a != b);
        assert!(b != a);
    }

    #[test]
    fn objects_have_ruby_truthiness() {
        assert_eq!(Value::scalar(true), Value::Object(Object::new()));
        assert!(Value::Object(Object::new()).query_state(State::Truthy));
    }

    #[test]
    fn nil_equality() {
        assert_eq!(Value::Nil, Value::Nil);
    }

    #[test]
    fn nils_have_ruby_truthiness() {
        assert_eq!(Value::scalar(false), Value::Nil);
        assert!(!Value::Nil.query_state(State::Truthy));

        assert_eq!(Value::scalar(false), Value::Nil);
        assert!(Value::scalar(true) != Value::Nil);
        assert!(Value::scalar("") != Value::Nil);
    }

    #[test]
    fn empty_equality() {
        let blank = Value::State(State::Blank);
        let empty = Value::State(State::Empty);
        // Truth table from https://stackoverflow.com/questions/885414/a-concise-explanation-of-nil-v-empty-v-blank-in-ruby-on-rails
        assert_eq!(empty, empty);
        assert_eq!(empty, blank);
        assert_eq!(empty, value!(""));
        assert_ne!(empty, value!(" "));
        assert_eq!(empty, value!([]));
        assert_ne!(empty, value!([nil]));
        assert_eq!(empty, value!({}));
        assert_ne!(empty, value!({ "a": nil }));
    }

    #[test]
    fn blank_equality() {
        let blank = Value::State(State::Blank);
        let empty = Value::State(State::Empty);
        // Truth table from https://stackoverflow.com/questions/885414/a-concise-explanation-of-nil-v-empty-v-blank-in-ruby-on-rails
        assert_eq!(blank, blank);
        assert_eq!(blank, empty);
        assert_eq!(blank, value!(nil));
        assert_eq!(blank, value!(false));
        assert_ne!(blank, value!(true));
        assert_ne!(blank, value!(0));
        assert_ne!(blank, value!(1));
        assert_eq!(blank, value!(""));
        assert_eq!(blank, value!(" "));
        assert_eq!(blank, value!([]));
        assert_ne!(blank, value!([nil]));
        assert_eq!(blank, value!({}));
        assert_ne!(blank, value!({ "a": nil }));
    }
}
