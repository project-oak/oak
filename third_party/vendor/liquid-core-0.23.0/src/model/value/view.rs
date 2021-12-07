use std::cmp::Ordering;
use std::fmt;

use kstring::KStringCow;

use super::DisplayCow;
use super::State;
use super::Value;
use crate::model::ArrayView;
use crate::model::ObjectView;
use crate::model::ScalarCow;

/// Accessor for Values.
pub trait ValueView: fmt::Debug {
    /// Get a `Debug` representation
    fn as_debug(&self) -> &dyn fmt::Debug;

    /// A `Display` for a `BoxedValue` rendered for the user.
    fn render(&self) -> DisplayCow<'_>;
    /// A `Display` for a `Value` as source code.
    fn source(&self) -> DisplayCow<'_>;
    /// Report the data type (generally for error reporting).
    fn type_name(&self) -> &'static str;
    /// Query the value's state
    fn query_state(&self, state: State) -> bool;

    /// Interpret as a string.
    fn to_kstr(&self) -> KStringCow<'_>;
    /// Convert to an owned type.
    fn to_value(&self) -> Value;

    /// Extracts the scalar value if it is a scalar.
    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        None
    }
    /// Tests whether this value is a scalar
    fn is_scalar(&self) -> bool {
        self.as_scalar().is_some()
    }

    /// Extracts the array value if it is an array.
    fn as_array(&self) -> Option<&dyn ArrayView> {
        None
    }
    /// Tests whether this value is an array
    fn is_array(&self) -> bool {
        self.as_array().is_some()
    }

    /// Extracts the object value if it is a object.
    fn as_object(&self) -> Option<&dyn ObjectView> {
        None
    }
    /// Tests whether this value is an object
    fn is_object(&self) -> bool {
        self.as_object().is_some()
    }

    /// Extracts the state if it is one
    fn as_state(&self) -> Option<State> {
        None
    }
    /// Tests whether this value is state
    fn is_state(&self) -> bool {
        self.as_state().is_some()
    }

    /// Tests whether this value is nil
    ///
    /// See the [Stack overflow table](https://stackoverflow.com/questions/885414/a-concise-explanation-of-nil-v-empty-v-blank-in-ruby-on-rails)
    fn is_nil(&self) -> bool {
        false
    }
}

impl<'v, V: ValueView + ?Sized> ValueView for &'v V {
    fn as_debug(&self) -> &dyn fmt::Debug {
        <V as ValueView>::as_debug(self)
    }

    fn render(&self) -> DisplayCow<'_> {
        <V as ValueView>::render(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        <V as ValueView>::source(self)
    }
    fn type_name(&self) -> &'static str {
        <V as ValueView>::type_name(self)
    }
    fn query_state(&self, state: State) -> bool {
        <V as ValueView>::query_state(self, state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        <V as ValueView>::to_kstr(self)
    }
    fn to_value(&self) -> Value {
        <V as ValueView>::to_value(self)
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        <V as ValueView>::as_scalar(self)
    }

    fn as_array(&self) -> Option<&dyn ArrayView> {
        <V as ValueView>::as_array(self)
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        <V as ValueView>::as_object(self)
    }

    fn as_state(&self) -> Option<State> {
        <V as ValueView>::as_state(self)
    }

    fn is_nil(&self) -> bool {
        <V as ValueView>::is_nil(self)
    }
}

static NIL: Value = Value::Nil;

impl<T: ValueView> ValueView for Option<T> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        forward(self).render()
    }
    fn source(&self) -> DisplayCow<'_> {
        forward(self).source()
    }
    fn type_name(&self) -> &'static str {
        forward(self).type_name()
    }
    fn query_state(&self, state: State) -> bool {
        forward(self).query_state(state)
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        forward(self).to_kstr()
    }
    fn to_value(&self) -> Value {
        forward(self).to_value()
    }

    fn as_scalar(&self) -> Option<ScalarCow<'_>> {
        forward(self).as_scalar()
    }

    fn as_array(&self) -> Option<&dyn ArrayView> {
        forward(self).as_array()
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        forward(self).as_object()
    }

    fn as_state(&self) -> Option<State> {
        forward(self).as_state()
    }

    fn is_nil(&self) -> bool {
        forward(self).is_nil()
    }
}

fn forward(o: &Option<impl ValueView>) -> &dyn ValueView {
    o.as_ref()
        .map(|v| v as &dyn ValueView)
        .unwrap_or(&NIL as &dyn ValueView)
}

/// `Value` comparison semantics for types implementing `ValueView`.
#[derive(Copy, Clone, Debug)]
pub struct ValueViewCmp<'v>(&'v dyn ValueView);

impl<'v> ValueViewCmp<'v> {
    /// `Value` comparison semantics for types implementing `ValueView`.
    pub fn new(v: &dyn ValueView) -> ValueViewCmp<'_> {
        ValueViewCmp(v)
    }
}

impl<'v> PartialEq<ValueViewCmp<'v>> for ValueViewCmp<'v> {
    fn eq(&self, other: &Self) -> bool {
        value_eq(self.0, other.0)
    }
}

impl<'v> PartialEq<i64> for ValueViewCmp<'v> {
    fn eq(&self, other: &i64) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<f64> for ValueViewCmp<'v> {
    fn eq(&self, other: &f64) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<bool> for ValueViewCmp<'v> {
    fn eq(&self, other: &bool) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<crate::model::scalar::DateTime> for ValueViewCmp<'v> {
    fn eq(&self, other: &crate::model::scalar::DateTime) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<crate::model::scalar::Date> for ValueViewCmp<'v> {
    fn eq(&self, other: &crate::model::scalar::Date) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<str> for ValueViewCmp<'v> {
    fn eq(&self, other: &str) -> bool {
        let other = KStringCow::from_ref(other);
        super::value_eq(self.0, &other)
    }
}

impl<'v> PartialEq<&'v str> for ValueViewCmp<'v> {
    fn eq(&self, other: &&str) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<String> for ValueViewCmp<'v> {
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl<'v> PartialEq<kstring::KString> for ValueViewCmp<'v> {
    fn eq(&self, other: &kstring::KString) -> bool {
        super::value_eq(self.0, &other.as_ref())
    }
}

impl<'v> PartialEq<kstring::KStringRef<'v>> for ValueViewCmp<'v> {
    fn eq(&self, other: &kstring::KStringRef<'v>) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialEq<kstring::KStringCow<'v>> for ValueViewCmp<'v> {
    fn eq(&self, other: &kstring::KStringCow<'v>) -> bool {
        super::value_eq(self.0, other)
    }
}

impl<'v> PartialOrd<ValueViewCmp<'v>> for ValueViewCmp<'v> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        value_cmp(self.0, other.0)
    }
}

pub(crate) fn value_eq(lhs: &dyn ValueView, rhs: &dyn ValueView) -> bool {
    if let (Some(x), Some(y)) = (lhs.as_array(), rhs.as_array()) {
        if x.size() != y.size() {
            return false;
        }
        return x.values().zip(y.values()).all(|(x, y)| value_eq(x, y));
    }

    if let (Some(x), Some(y)) = (lhs.as_object(), rhs.as_object()) {
        if x.size() != y.size() {
            return false;
        }
        return x
            .iter()
            .all(|(key, value)| y.get(key.as_str()).map_or(false, |v| value_eq(v, value)));
    }

    if lhs.is_nil() && rhs.is_nil() {
        return true;
    }

    if let Some(state) = lhs.as_state() {
        return rhs.query_state(state);
    } else if let Some(state) = rhs.as_state() {
        return lhs.query_state(state);
    }

    match (lhs.as_scalar(), rhs.as_scalar()) {
        (Some(x), Some(y)) => return x == y,
        (None, None) => (),
        // encode Ruby truthiness: all values except false and nil are true
        (Some(x), _) => {
            if rhs.is_nil() {
                return !x.to_bool().unwrap_or(true);
            } else {
                return x.to_bool().unwrap_or(false);
            }
        }
        (_, Some(x)) => {
            if lhs.is_nil() {
                return !x.to_bool().unwrap_or(true);
            } else {
                return x.to_bool().unwrap_or(false);
            }
        }
    }

    false
}

pub(crate) fn value_cmp(lhs: &dyn ValueView, rhs: &dyn ValueView) -> Option<Ordering> {
    if let (Some(x), Some(y)) = (lhs.as_scalar(), rhs.as_scalar()) {
        return x.partial_cmp(&y);
    }

    if let (Some(x), Some(y)) = (lhs.as_array(), rhs.as_array()) {
        return x
            .values()
            .map(|v| ValueViewCmp(v))
            .partial_cmp(y.values().map(|v| ValueViewCmp(v)));
    }

    if let (Some(x), Some(y)) = (lhs.as_object(), rhs.as_object()) {
        return x
            .iter()
            .map(|(k, v)| (k, ValueViewCmp(v)))
            .partial_cmp(y.iter().map(|(k, v)| (k, ValueViewCmp(v))));
    }

    None
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_debug() {
        let scalar = 5;
        println!("{:?}", scalar);
        let view: &dyn ValueView = &scalar;
        println!("{:?}", view);
        let debug: &dyn fmt::Debug = view.as_debug();
        println!("{:?}", debug);
    }
}
