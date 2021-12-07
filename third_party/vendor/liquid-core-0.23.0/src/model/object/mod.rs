//! Type representing a Liquid object, payload of the `Value::Object` variant

pub mod map;
mod ser;

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt;

use kstring::KStringCow;

use crate::model::value::DisplayCow;
use crate::model::State;
use crate::model::{Value, ValueView};

pub use map::Object;
pub use ser::to_object;

/// Accessor for objects.
pub trait ObjectView: ValueView {
    /// Cast to ValueView
    fn as_value(&self) -> &dyn ValueView;

    /// Returns the number of elements.
    fn size(&self) -> i64;

    /// Keys available for lookup.
    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = KStringCow<'k>> + 'k>;
    /// Keys available for lookup.
    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k>;
    /// Returns an iterator .
    fn iter<'k>(&'k self) -> Box<dyn Iterator<Item = (KStringCow<'k>, &'k dyn ValueView)> + 'k>;

    /// Access a contained `BoxedValue`.
    fn contains_key(&self, index: &str) -> bool;
    /// Access a contained `Value`.
    fn get<'s>(&'s self, index: &str) -> Option<&'s dyn ValueView>;
}

impl ValueView for Object {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectRender { s: self }))
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectSource { s: self }))
    }
    fn type_name(&self) -> &'static str {
        "object"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue | State::Empty | State::Blank => self.is_empty(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        let s = ObjectRender { s: self }.to_string();
        KStringCow::from_string(s)
    }
    fn to_value(&self) -> Value {
        Value::Object(self.clone())
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        Some(self)
    }
}

impl ObjectView for Object {
    fn as_value(&self) -> &dyn ValueView {
        self
    }

    fn size(&self) -> i64 {
        self.len() as i64
    }

    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = KStringCow<'k>> + 'k> {
        let keys = Object::keys(self).map(|s| s.as_ref().into());
        Box::new(keys)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        let i = Object::values(self).map(|v| v.as_view());
        Box::new(i)
    }

    fn iter<'k>(&'k self) -> Box<dyn Iterator<Item = (KStringCow<'k>, &'k dyn ValueView)> + 'k> {
        let i = Object::iter(self).map(|(k, v)| (k.as_str().into(), v.as_view()));
        Box::new(i)
    }

    fn contains_key(&self, index: &str) -> bool {
        Object::contains_key(self, index)
    }

    fn get<'s>(&'s self, index: &str) -> Option<&'s dyn ValueView> {
        Object::get(self, index).map(|v| v.as_view())
    }
}

impl<'o, O: ObjectView + ?Sized> ObjectView for &'o O {
    fn as_value(&self) -> &dyn ValueView {
        <O as ObjectView>::as_value(self)
    }

    fn size(&self) -> i64 {
        <O as ObjectView>::size(self)
    }

    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = KStringCow<'k>> + 'k> {
        <O as ObjectView>::keys(self)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        <O as ObjectView>::values(self)
    }

    fn iter<'k>(&'k self) -> Box<dyn Iterator<Item = (KStringCow<'k>, &'k dyn ValueView)> + 'k> {
        <O as ObjectView>::iter(self)
    }

    fn contains_key(&self, index: &str) -> bool {
        <O as ObjectView>::contains_key(self, index)
    }

    fn get<'s>(&'s self, index: &str) -> Option<&'s dyn ValueView> {
        <O as ObjectView>::get(self, index)
    }
}

/// Owned object index
pub trait ObjectIndex:
    fmt::Debug + fmt::Display + Ord + std::hash::Hash + Eq + std::borrow::Borrow<str>
{
    /// Borrow the index
    fn as_index(&self) -> &str;
}

impl ObjectIndex for String {
    fn as_index(&self) -> &str {
        self.as_str()
    }
}

impl ObjectIndex for kstring::KString {
    fn as_index(&self) -> &str {
        self.as_str()
    }
}

impl<'s> ObjectIndex for kstring::KStringRef<'s> {
    fn as_index(&self) -> &str {
        self.as_str()
    }
}

impl<'s> ObjectIndex for kstring::KStringCow<'s> {
    fn as_index(&self) -> &str {
        self.as_str()
    }
}

impl<K: ObjectIndex, V: ValueView, S: ::std::hash::BuildHasher> ValueView for HashMap<K, V, S> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectRender { s: self }))
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectSource { s: self }))
    }
    fn type_name(&self) -> &'static str {
        "object"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue | State::Empty | State::Blank => self.is_empty(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        let s = ObjectRender { s: self }.to_string();
        KStringCow::from_string(s)
    }
    fn to_value(&self) -> Value {
        Value::Object(
            self.iter()
                .map(|(k, v)| (kstring::KString::from_ref(k.as_index()), v.to_value()))
                .collect(),
        )
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        Some(self)
    }
}

impl<K: ObjectIndex, V: ValueView, S: ::std::hash::BuildHasher> ObjectView for HashMap<K, V, S> {
    fn as_value(&self) -> &dyn ValueView {
        self
    }

    fn size(&self) -> i64 {
        self.len() as i64
    }

    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = KStringCow<'k>> + 'k> {
        let keys = HashMap::keys(self).map(|s| s.as_index().into());
        Box::new(keys)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        let i = HashMap::values(self).map(as_view);
        Box::new(i)
    }

    fn iter<'k>(&'k self) -> Box<dyn Iterator<Item = (KStringCow<'k>, &'k dyn ValueView)> + 'k> {
        let i = HashMap::iter(self).map(|(k, v)| (k.as_index().into(), as_view(v)));
        Box::new(i)
    }

    fn contains_key(&self, index: &str) -> bool {
        HashMap::contains_key(self, index)
    }

    fn get<'s>(&'s self, index: &str) -> Option<&'s dyn ValueView> {
        HashMap::get(self, index).map(as_view)
    }
}

impl<K: ObjectIndex, V: ValueView> ValueView for BTreeMap<K, V> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectRender { s: self }))
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ObjectSource { s: self }))
    }
    fn type_name(&self) -> &'static str {
        "object"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue | State::Empty | State::Blank => self.is_empty(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        let s = ObjectRender { s: self }.to_string();
        KStringCow::from_string(s)
    }
    fn to_value(&self) -> Value {
        Value::Object(
            self.iter()
                .map(|(k, v)| (kstring::KString::from_ref(k.as_index()), v.to_value()))
                .collect(),
        )
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        Some(self)
    }
}

impl<K: ObjectIndex, V: ValueView> ObjectView for BTreeMap<K, V> {
    fn as_value(&self) -> &dyn ValueView {
        self
    }

    fn size(&self) -> i64 {
        self.len() as i64
    }

    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = KStringCow<'k>> + 'k> {
        let keys = BTreeMap::keys(self).map(|s| s.as_index().into());
        Box::new(keys)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        let i = BTreeMap::values(self).map(as_view);
        Box::new(i)
    }

    fn iter<'k>(&'k self) -> Box<dyn Iterator<Item = (KStringCow<'k>, &'k dyn ValueView)> + 'k> {
        let i = BTreeMap::iter(self).map(|(k, v)| (k.as_index().into(), as_view(v)));
        Box::new(i)
    }

    fn contains_key(&self, index: &str) -> bool {
        BTreeMap::contains_key(self, index)
    }

    fn get<'s>(&'s self, index: &str) -> Option<&'s dyn ValueView> {
        BTreeMap::get(self, index).map(as_view)
    }
}

fn as_view<T: ValueView>(value: &T) -> &dyn ValueView {
    value
}

#[derive(Debug)]
/// Helper for `ObjectView::source`
pub struct ObjectSource<'s, O: ObjectView> {
    s: &'s O,
}

impl<'s, O: ObjectView> ObjectSource<'s, O> {
    #[doc(hidden)]
    pub fn new(other: &'s O) -> Self {
        Self { s: other }
    }
}

impl<'s, O: ObjectView> fmt::Display for ObjectSource<'s, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (k, v) in self.s.iter() {
            write!(f, r#""{}": {}, "#, k, v.render())?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[derive(Debug)]
/// Helper for `ObjectView::render`
pub struct ObjectRender<'s, O: ObjectView> {
    s: &'s O,
}

impl<'s, O: ObjectView> ObjectRender<'s, O> {
    #[doc(hidden)]
    pub fn new(other: &'s O) -> Self {
        Self { s: other }
    }
}

impl<'s, O: ObjectView> fmt::Display for ObjectRender<'s, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in self.s.iter() {
            write!(f, "{}{}", k, v.render())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_object() {
        let obj = Object::new();
        println!("{}", obj.source());
        let object: &dyn ObjectView = &obj;
        println!("{}", object.source());
        let view: &dyn ValueView = object.as_value();
        println!("{}", view.source());
    }
}
