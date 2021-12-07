//! A Liquid scalar value

#![allow(clippy::eq_op)]

mod date;
mod datetime;
pub(crate) mod ser;

use std::cmp::Ordering;
use std::{borrow::Cow, fmt};

use kstring::KString;
use kstring::KStringCow;
use kstring::KStringRef;

use crate::model::value::{DisplayCow, State};
use crate::model::{Value, ValueView};

pub use date::*;
pub use datetime::*;
pub use ser::to_scalar;

/// A Liquid scalar value
#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct ScalarCow<'s>(ScalarCowEnum<'s>);

/// A Liquid scalar value
pub type Scalar = ScalarCow<'static>;

/// An enum to represent different value types
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
enum ScalarCowEnum<'s> {
    Integer(i64),
    Float(f64),
    Bool(bool),
    DateTime(DateTime),
    Date(Date),
    Str(KStringCow<'s>),
}

impl<'s> ScalarCow<'s> {
    /// Convert a value into a `ScalarCow`.
    pub fn new<T: Into<Self>>(value: T) -> Self {
        value.into()
    }

    /// Create an owned version of the value.
    pub fn into_owned(self) -> Scalar {
        match self.0 {
            ScalarCowEnum::Integer(x) => Scalar::new(x),
            ScalarCowEnum::Float(x) => Scalar::new(x),
            ScalarCowEnum::Bool(x) => Scalar::new(x),
            ScalarCowEnum::DateTime(x) => Scalar::new(x),
            ScalarCowEnum::Date(x) => Scalar::new(x),
            ScalarCowEnum::Str(x) => Scalar::new(x.into_owned()),
        }
    }

    /// Create a reference to the value.
    pub fn as_ref<'r: 's>(&'r self) -> ScalarCow<'r> {
        match self.0 {
            ScalarCowEnum::Integer(x) => ScalarCow::new(x),
            ScalarCowEnum::Float(x) => ScalarCow::new(x),
            ScalarCowEnum::Bool(x) => ScalarCow::new(x),
            ScalarCowEnum::DateTime(x) => ScalarCow::new(x),
            ScalarCowEnum::Date(x) => ScalarCow::new(x),
            ScalarCowEnum::Str(ref x) => ScalarCow::new(x.as_ref()),
        }
    }

    /// Create a reference to the value.
    pub fn as_view<'r: 's>(&'r self) -> &'s dyn ValueView {
        match self.0 {
            ScalarCowEnum::Integer(ref x) => x,
            ScalarCowEnum::Float(ref x) => x,
            ScalarCowEnum::Bool(ref x) => x,
            ScalarCowEnum::DateTime(ref x) => x,
            ScalarCowEnum::Date(ref x) => x,
            ScalarCowEnum::Str(ref x) => x,
        }
    }

    /// Convert to a string.
    pub fn into_string(self) -> KString {
        match self.0 {
            ScalarCowEnum::Integer(x) => x.to_string().into(),
            ScalarCowEnum::Float(x) => x.to_string().into(),
            ScalarCowEnum::Bool(x) => x.to_string().into(),
            ScalarCowEnum::DateTime(x) => x.to_string().into(),
            ScalarCowEnum::Date(x) => x.to_string().into(),
            ScalarCowEnum::Str(x) => x.into_owned(),
        }
    }

    /// Interpret as an integer, if possible
    pub fn to_integer(&self) -> Option<i64> {
        match self.0 {
            ScalarCowEnum::Integer(ref x) => Some(*x),
            ScalarCowEnum::Str(ref x) => x.parse::<i64>().ok(),
            _ => None,
        }
    }

    /// Interpret as a float, if possible
    pub fn to_float(&self) -> Option<f64> {
        match self.0 {
            ScalarCowEnum::Integer(ref x) => Some(*x as f64),
            ScalarCowEnum::Float(ref x) => Some(*x),
            ScalarCowEnum::Str(ref x) => x.parse::<f64>().ok(),
            _ => None,
        }
    }

    /// Interpret as a bool, if possible
    pub fn to_bool(&self) -> Option<bool> {
        match self.0 {
            ScalarCowEnum::Bool(ref x) => Some(*x),
            _ => None,
        }
    }

    /// Interpret as a date time, if possible
    pub fn to_date_time(&self) -> Option<DateTime> {
        match self.0 {
            ScalarCowEnum::DateTime(ref x) => Some(*x),
            ScalarCowEnum::Str(ref x) => DateTime::from_str(x.as_str()),
            _ => None,
        }
    }

    /// Interpret as a date time, if possible
    pub fn to_date(&self) -> Option<Date> {
        match self.0 {
            ScalarCowEnum::DateTime(ref x) => Some(x.date()),
            ScalarCowEnum::Date(ref x) => Some(*x),
            ScalarCowEnum::Str(ref x) => Date::from_str(x.as_str()),
            _ => None,
        }
    }

    /// Interpret as a Cow str, borrowing if possible
    pub fn into_cow_str(self) -> Cow<'s, str> {
        match self {
            Self(ScalarCowEnum::Str(x)) => x.into_cow_str(),
            other => other.into_string().into_cow_str(),
        }
    }
}

impl<'s> fmt::Debug for ScalarCow<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<'s> ValueView for ScalarCow<'s> {
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
        Some(self.as_ref())
    }
}

impl<'s> PartialEq<ScalarCow<'s>> for ScalarCow<'s> {
    fn eq(&self, other: &Self) -> bool {
        scalar_eq(self, other)
    }
}

impl<'s> PartialOrd<ScalarCow<'s>> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        scalar_cmp(self, other)
    }
}

impl ValueView for i64 {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn type_name(&self) -> &'static str {
        "whole number"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue => false,
            State::Empty => false,
            State::Blank => false,
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.render().to_string().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(*self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

impl<'s> From<i64> for ScalarCow<'s> {
    fn from(s: i64) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Integer(s),
        }
    }
}

impl<'s> PartialEq<i64> for ScalarCow<'s> {
    fn eq(&self, other: &i64) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<i64> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        let other = (*other).into();
        scalar_cmp(self, &other)
    }
}

macro_rules! impl_copyable {
    ($user: ty, $internal: ty) => {
        impl ValueView for $user {
            fn as_debug(&self) -> &dyn fmt::Debug {
                self
            }

            fn render(&self) -> DisplayCow<'_> {
                DisplayCow::Borrowed(self)
            }
            fn source(&self) -> DisplayCow<'_> {
                DisplayCow::Borrowed(self)
            }
            fn type_name(&self) -> &'static str {
                <$internal>::from(*self).type_name()
            }
            fn query_state(&self, state: State) -> bool {
                <$internal>::from(*self).query_state(state)
            }

            fn to_kstr(&self) -> KStringCow<'_> {
                self.render().to_string().into()
            }
            fn to_value(&self) -> Value {
                <$internal>::from(*self).to_value()
            }

            fn as_scalar(&self) -> Option<ScalarCow<'_>> {
                Some(ScalarCow::new(<$internal>::from(*self)))
            }
        }

        impl<'s> From<$user> for ScalarCow<'s> {
            fn from(s: $user) -> Self {
                ScalarCow::from(<$internal>::from(s))
            }
        }

        impl<'s> PartialEq<$user> for ScalarCow<'s> {
            fn eq(&self, other: &$user) -> bool {
                let other = <$internal>::from(*other).into();
                scalar_eq(self, &other)
            }
        }

        impl<'s> PartialOrd<$user> for ScalarCow<'s> {
            fn partial_cmp(&self, other: &$user) -> Option<Ordering> {
                let other = <$internal>::from(*other).into();
                scalar_cmp(self, &other)
            }
        }
    };
}

impl_copyable!(u8, i64);
impl_copyable!(i8, i64);
impl_copyable!(u16, i64);
impl_copyable!(i16, i64);
impl_copyable!(u32, i64);
impl_copyable!(i32, i64);

impl ValueView for f64 {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn type_name(&self) -> &'static str {
        "fractional number"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue => false,
            State::Empty => false,
            State::Blank => false,
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.render().to_string().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(*self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

impl<'s> From<f64> for ScalarCow<'s> {
    fn from(s: f64) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Float(s),
        }
    }
}

impl<'s> PartialEq<f64> for ScalarCow<'s> {
    fn eq(&self, other: &f64) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<f64> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        let other = (*other).into();
        scalar_cmp(self, &other)
    }
}

impl_copyable!(f32, f64);

impl ValueView for bool {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn type_name(&self) -> &'static str {
        "boolean"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => *self,
            State::DefaultValue => !self,
            State::Empty => false,
            State::Blank => !self,
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.render().to_string().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(*self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

impl<'s> From<bool> for ScalarCow<'s> {
    fn from(s: bool) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Bool(s),
        }
    }
}

impl<'s> PartialEq<bool> for ScalarCow<'s> {
    fn eq(&self, other: &bool) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<bool> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &bool) -> Option<Ordering> {
        let other = (*other).into();
        scalar_cmp(self, &other)
    }
}

impl ValueView for DateTime {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn type_name(&self) -> &'static str {
        "date time"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue => false,
            State::Empty => false,
            State::Blank => false,
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.render().to_string().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(*self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

impl<'s> From<DateTime> for ScalarCow<'s> {
    fn from(s: DateTime) -> Self {
        ScalarCow {
            0: ScalarCowEnum::DateTime(s),
        }
    }
}

impl<'s> PartialEq<DateTime> for ScalarCow<'s> {
    fn eq(&self, other: &DateTime) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<DateTime> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &DateTime) -> Option<Ordering> {
        let other = (*other).into();
        scalar_cmp(self, &other)
    }
}

impl ValueView for Date {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn type_name(&self) -> &'static str {
        "date"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue => false,
            State::Empty => false,
            State::Blank => false,
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.render().to_string().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(*self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

impl<'s> From<Date> for ScalarCow<'s> {
    fn from(s: Date) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Date(s),
        }
    }
}

impl<'s> PartialEq<Date> for ScalarCow<'s> {
    fn eq(&self, other: &Date) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<Date> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &Date) -> Option<Ordering> {
        let other = (*other).into();
        scalar_cmp(self, &other)
    }
}

impl<'s> ValueView for &'s str {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(StrSource { s: self }))
    }
    fn type_name(&self) -> &'static str {
        "string"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue => self.is_empty(),
            State::Empty => self.is_empty(),
            State::Blank => self.trim().is_empty(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        (*self).into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(ScalarCow::new(KString::from_ref(self)))
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(*self))
    }
}

struct StrSource<'s> {
    s: &'s str,
}

impl<'s> fmt::Display for StrSource<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, r#""{}""#, self.s)
    }
}

impl<'s> From<&'s str> for ScalarCow<'s> {
    fn from(s: &'s str) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.into()),
        }
    }
}

impl<'s> PartialEq<str> for ScalarCow<'s> {
    fn eq(&self, other: &str) -> bool {
        let other = other.into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialEq<&'s str> for ScalarCow<'s> {
    fn eq(&self, other: &&str) -> bool {
        let other = (*other).into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<str> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        let other = other.into();
        scalar_cmp(self, &other)
    }
}

impl ValueView for String {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(StrSource { s: self.as_str() }))
    }
    fn type_name(&self) -> &'static str {
        ValueView::type_name(&self.as_str())
    }
    fn query_state(&self, state: State) -> bool {
        ValueView::query_state(&self.as_str(), state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.as_str().into()
    }
    fn to_value(&self) -> Value {
        ValueView::to_value(&self.as_str())
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(self.as_str()))
    }
}

impl<'s> From<String> for ScalarCow<'s> {
    fn from(s: String) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.into()),
        }
    }
}

impl<'s> From<&'s String> for ScalarCow<'s> {
    fn from(s: &'s String) -> ScalarCow<'s> {
        ScalarCow {
            0: ScalarCowEnum::Str(s.as_str().into()),
        }
    }
}

impl<'s> PartialEq<String> for ScalarCow<'s> {
    fn eq(&self, other: &String) -> bool {
        let other = other.into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<String> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        let other = other.into();
        scalar_cmp(self, &other)
    }
}

impl ValueView for KString {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(StrSource { s: self.as_str() }))
    }
    fn type_name(&self) -> &'static str {
        ValueView::type_name(&self.as_str())
    }
    fn query_state(&self, state: State) -> bool {
        ValueView::query_state(&self.as_str(), state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.as_ref().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(Scalar::new(self.clone()))
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(self))
    }
}

impl<'s> From<KString> for ScalarCow<'s> {
    fn from(s: KString) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.into()),
        }
    }
}

impl<'s> From<&'s KString> for ScalarCow<'s> {
    fn from(s: &'s KString) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.as_ref().into()),
        }
    }
}

impl<'s> PartialEq<KString> for ScalarCow<'s> {
    fn eq(&self, other: &KString) -> bool {
        let other = other.into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<KString> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &KString) -> Option<Ordering> {
        let other = other.into();
        scalar_cmp(self, &other)
    }
}

impl<'s> ValueView for KStringCow<'s> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(StrSource { s: self.as_str() }))
    }
    fn type_name(&self) -> &'static str {
        ValueView::type_name(&self.as_str())
    }
    fn query_state(&self, state: State) -> bool {
        ValueView::query_state(&self.as_str(), state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.clone()
    }
    fn to_value(&self) -> Value {
        Value::scalar(Scalar::new(self.clone().into_owned()))
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(self))
    }
}

impl<'s> From<KStringCow<'s>> for ScalarCow<'s> {
    fn from(s: KStringCow<'s>) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s),
        }
    }
}

impl<'s> From<&'s KStringCow<'s>> for ScalarCow<'s> {
    fn from(s: &'s KStringCow<'s>) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.clone()),
        }
    }
}

impl<'s> PartialEq<KStringCow<'s>> for ScalarCow<'s> {
    fn eq(&self, other: &KStringCow<'s>) -> bool {
        let other = other.into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<KStringCow<'s>> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &KStringCow<'s>) -> Option<Ordering> {
        let other = other.into();
        scalar_cmp(self, &other)
    }
}

impl<'s> ValueView for KStringRef<'s> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(StrSource { s: self.as_str() }))
    }
    fn type_name(&self) -> &'static str {
        ValueView::type_name(&self.as_str())
    }
    fn query_state(&self, state: State) -> bool {
        ValueView::query_state(&self.as_str(), state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        self.clone().into()
    }
    fn to_value(&self) -> Value {
        Value::scalar(Scalar::new(self.to_owned()))
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        Some(ScalarCow::new(self))
    }
}

impl<'s> From<KStringRef<'s>> for ScalarCow<'s> {
    fn from(s: KStringRef<'s>) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.into()),
        }
    }
}

impl<'s> From<&'s KStringRef<'s>> for ScalarCow<'s> {
    fn from(s: &'s KStringRef<'s>) -> Self {
        ScalarCow {
            0: ScalarCowEnum::Str(s.into()),
        }
    }
}

impl<'s> PartialEq<KStringRef<'s>> for ScalarCow<'s> {
    fn eq(&self, other: &KStringRef<'s>) -> bool {
        let other = other.into();
        scalar_eq(self, &other)
    }
}

impl<'s> PartialOrd<KStringRef<'s>> for ScalarCow<'s> {
    fn partial_cmp(&self, other: &KStringRef<'s>) -> Option<Ordering> {
        let other = other.into();
        scalar_cmp(self, &other)
    }
}

impl<'s> Eq for ScalarCow<'s> {}

fn scalar_eq<'s>(lhs: &ScalarCow<'s>, rhs: &ScalarCow<'s>) -> bool {
    match (&lhs.0, &rhs.0) {
        (&ScalarCowEnum::Integer(x), &ScalarCowEnum::Integer(y)) => x == y,
        (&ScalarCowEnum::Integer(x), &ScalarCowEnum::Float(y)) => (x as f64) == y,
        (&ScalarCowEnum::Float(x), &ScalarCowEnum::Integer(y)) => x == (y as f64),
        (&ScalarCowEnum::Float(x), &ScalarCowEnum::Float(y)) => x == y,
        (&ScalarCowEnum::Bool(x), &ScalarCowEnum::Bool(y)) => x == y,
        (&ScalarCowEnum::DateTime(x), &ScalarCowEnum::DateTime(y)) => x == y,
        (&ScalarCowEnum::Date(x), &ScalarCowEnum::Date(y)) => x == y,
        (&ScalarCowEnum::DateTime(x), &ScalarCowEnum::Date(y)) => x == x.with_date(y),
        (&ScalarCowEnum::Date(x), &ScalarCowEnum::DateTime(y)) => y.with_date(x) == y,
        (&ScalarCowEnum::Str(ref x), &ScalarCowEnum::Str(ref y)) => x == y,
        // encode Ruby truthiness: all values except false and nil are true
        (_, &ScalarCowEnum::Bool(b)) | (&ScalarCowEnum::Bool(b), _) => b,
        _ => false,
    }
}

fn scalar_cmp<'s>(lhs: &ScalarCow<'s>, rhs: &ScalarCow<'s>) -> Option<Ordering> {
    match (&lhs.0, &rhs.0) {
        (&ScalarCowEnum::Integer(x), &ScalarCowEnum::Integer(y)) => x.partial_cmp(&y),
        (&ScalarCowEnum::Integer(x), &ScalarCowEnum::Float(y)) => (x as f64).partial_cmp(&y),
        (&ScalarCowEnum::Float(x), &ScalarCowEnum::Integer(y)) => x.partial_cmp(&(y as f64)),
        (&ScalarCowEnum::Float(x), &ScalarCowEnum::Float(y)) => x.partial_cmp(&y),
        (&ScalarCowEnum::Bool(x), &ScalarCowEnum::Bool(y)) => x.partial_cmp(&y),
        (&ScalarCowEnum::DateTime(x), &ScalarCowEnum::DateTime(y)) => x.partial_cmp(&y),
        (&ScalarCowEnum::Date(x), &ScalarCowEnum::Date(y)) => x.partial_cmp(&y),
        (&ScalarCowEnum::DateTime(x), &ScalarCowEnum::Date(y)) => x.partial_cmp(&x.with_date(y)),
        (&ScalarCowEnum::Date(x), &ScalarCowEnum::DateTime(y)) => y.with_date(x).partial_cmp(&y),
        (&ScalarCowEnum::Str(ref x), &ScalarCowEnum::Str(ref y)) => x.partial_cmp(y),
        _ => None,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    static TRUE: ScalarCow<'_> = ScalarCow(ScalarCowEnum::Bool(true));
    static FALSE: ScalarCow<'_> = ScalarCow(ScalarCowEnum::Bool(false));

    #[test]
    fn test_to_str_bool() {
        assert_eq!(TRUE.to_kstr(), "true");
    }

    #[test]
    fn test_to_str_integer() {
        let val: ScalarCow<'_> = 42i64.into();
        assert_eq!(val.to_kstr(), "42");
    }

    #[test]
    fn test_to_str_float() {
        let val: ScalarCow<'_> = 42f64.into();
        assert_eq!(val.to_kstr(), "42");

        let val: ScalarCow<'_> = 42.34.into();
        assert_eq!(val.to_kstr(), "42.34");
    }

    #[test]
    fn test_to_str_str() {
        let val: ScalarCow<'_> = "foobar".into();
        assert_eq!(val.to_kstr(), "foobar");
    }

    #[test]
    fn test_to_integer_bool() {
        assert_eq!(TRUE.to_integer(), None);
    }

    #[test]
    fn test_to_integer_integer() {
        let val: ScalarCow<'_> = 42i64.into();
        assert_eq!(val.to_integer(), Some(42i64));
    }

    #[test]
    fn test_to_integer_float() {
        let val: ScalarCow<'_> = 42f64.into();
        assert_eq!(val.to_integer(), None);

        let val: ScalarCow<'_> = 42.34.into();
        assert_eq!(val.to_integer(), None);
    }

    #[test]
    fn test_to_integer_str() {
        let val: ScalarCow<'_> = "foobar".into();
        assert_eq!(val.to_integer(), None);

        let val: ScalarCow<'_> = "42.34".into();
        assert_eq!(val.to_integer(), None);

        let val: ScalarCow<'_> = "42".into();
        assert_eq!(val.to_integer(), Some(42));
    }

    #[test]
    fn test_to_float_bool() {
        assert_eq!(TRUE.to_float(), None);
    }

    #[test]
    fn test_to_float_integer() {
        let val: ScalarCow<'_> = 42i64.into();
        assert_eq!(val.to_float(), Some(42f64));
    }

    #[test]
    fn test_to_float_float() {
        let val: ScalarCow<'_> = 42f64.into();
        assert_eq!(val.to_float(), Some(42f64));

        let val: ScalarCow<'_> = 42.34.into();
        assert_eq!(val.to_float(), Some(42.34));
    }

    #[test]
    fn test_to_float_str() {
        let val: ScalarCow<'_> = "foobar".into();
        assert_eq!(val.to_float(), None);

        let val: ScalarCow<'_> = "42.34".into();
        assert_eq!(val.to_float(), Some(42.34));

        let val: ScalarCow<'_> = "42".into();
        assert_eq!(val.to_float(), Some(42f64));
    }

    #[test]
    fn test_to_bool_bool() {
        assert_eq!(TRUE.to_bool(), Some(true));
    }

    #[test]
    fn test_to_bool_integer() {
        let val: ScalarCow<'_> = 42i64.into();
        assert_eq!(val.to_bool(), None);
    }

    #[test]
    fn test_to_bool_float() {
        let val: ScalarCow<'_> = 42f64.into();
        assert_eq!(val.to_bool(), None);

        let val: ScalarCow<'_> = 42.34.into();
        assert_eq!(val.to_bool(), None);
    }

    #[test]
    fn test_to_bool_str() {
        let val: ScalarCow<'_> = "foobar".into();
        assert_eq!(val.to_bool(), None);

        let val: ScalarCow<'_> = "true".into();
        assert_eq!(val.to_bool(), None);

        let val: ScalarCow<'_> = "false".into();
        assert_eq!(val.to_bool(), None);
    }

    #[test]
    fn integer_equality() {
        let val: ScalarCow<'_> = 42i64.into();
        let zero: ScalarCow<'_> = 0i64.into();
        assert_eq!(val, val);
        assert_eq!(zero, zero);
        assert!(val != zero);
        assert!(zero != val);
    }

    #[test]
    fn integers_have_ruby_truthiness() {
        let val: ScalarCow<'_> = 42i64.into();
        let zero: ScalarCow<'_> = 0i64.into();
        assert_eq!(TRUE, val);
        assert_eq!(val, TRUE);
        assert!(val.query_state(State::Truthy));

        assert_eq!(TRUE, zero);
        assert_eq!(zero, TRUE);
        assert!(zero.query_state(State::Truthy));
    }

    #[test]
    fn float_equality() {
        let val: ScalarCow<'_> = 42f64.into();
        let zero: ScalarCow<'_> = 0f64.into();
        assert_eq!(val, val);
        assert_eq!(zero, zero);
        assert!(val != zero);
        assert!(zero != val);
    }

    #[test]
    fn floats_have_ruby_truthiness() {
        let val: ScalarCow<'_> = 42f64.into();
        let zero: ScalarCow<'_> = 0f64.into();
        assert_eq!(TRUE, val);
        assert_eq!(val, TRUE);
        assert!(val.query_state(State::Truthy));

        assert_eq!(TRUE, zero);
        assert_eq!(zero, TRUE);
        assert!(zero.query_state(State::Truthy));
    }

    #[test]
    fn boolean_equality() {
        assert_eq!(TRUE, TRUE);
        assert_eq!(FALSE, FALSE);
        assert!(FALSE != TRUE);
        assert!(TRUE != FALSE);
    }

    #[test]
    fn booleans_have_ruby_truthiness() {
        assert!(TRUE.query_state(State::Truthy));
        assert!(!FALSE.query_state(State::Truthy));
    }

    #[test]
    fn string_equality() {
        let alpha: ScalarCow<'_> = "alpha".into();
        let beta: ScalarCow<'_> = "beta".into();
        let empty: ScalarCow<'_> = "".into();
        assert_eq!(alpha, alpha);
        assert_eq!(empty, empty);
        assert!(alpha != beta);
        assert!(beta != alpha);
    }

    #[test]
    fn strings_have_ruby_truthiness() {
        // all strings in ruby are true
        let alpha: ScalarCow<'_> = "alpha".into();
        let empty: ScalarCow<'_> = "".into();
        assert_eq!(TRUE, alpha);
        assert_eq!(alpha, TRUE);
        assert!(alpha.query_state(State::Truthy));

        assert_eq!(TRUE, empty);
        assert_eq!(empty, TRUE);
        assert!(empty.query_state(State::Truthy));
    }

    #[test]
    fn borrows_from_scalar_cow() {
        fn is_borrowed(cow: Cow<'_, str>) -> bool {
            match cow {
                Cow::Borrowed(_) => true,
                Cow::Owned(_) => false,
            }
        }

        let s: String = "gamma".into();
        let sc: ScalarCow<'_> = s.into();

        // clones instead of borrowing
        {
            fn extract_cow_str(value: &dyn ValueView) -> Cow<'_, str> {
                value.to_kstr().into_cow_str()
            }
            assert_eq!(is_borrowed(extract_cow_str(sc.as_view())), false);
        }

        // borrows successfully!
        {
            fn extract_cow_str(value: &dyn ValueView) -> Cow<'_, str> {
                value.as_scalar().unwrap().into_cow_str()
            }
            assert_eq!(is_borrowed(extract_cow_str(&sc)), true);
        }
    }
}
