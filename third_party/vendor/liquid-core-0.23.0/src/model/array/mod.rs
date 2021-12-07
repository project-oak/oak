//! Type representing a Liquid array, payload of the `Value::Array` variant

use std::fmt;

use kstring::KStringCow;

use crate::model::value::DisplayCow;
use crate::model::State;
use crate::model::Value;
use crate::model::ValueView;

/// Accessor for arrays.
pub trait ArrayView: ValueView {
    /// Cast to ValueView
    fn as_value(&self) -> &dyn ValueView;

    /// Returns the number of elements.
    fn size(&self) -> i64;

    /// Returns an iterator .
    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k>;

    /// Access a contained `Value`.
    fn contains_key(&self, index: i64) -> bool;
    /// Access a contained `Value`.
    fn get(&self, index: i64) -> Option<&dyn ValueView>;
    /// Returns the first element.
    fn first(&self) -> Option<&dyn ValueView> {
        self.get(0)
    }
    /// Returns the last element.
    fn last(&self) -> Option<&dyn ValueView> {
        self.get(-1)
    }
}

/// Type representing a Liquid array, payload of the `Value::Array` variant
pub type Array = Vec<Value>;

impl<T: ValueView> ValueView for Vec<T> {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ArrayRender { s: self }))
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(ArraySource { s: self }))
    }
    fn type_name(&self) -> &'static str {
        "array"
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => true,
            State::DefaultValue | State::Empty | State::Blank => self.is_empty(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        let s = ArrayRender { s: self }.to_string();
        KStringCow::from_string(s)
    }
    fn to_value(&self) -> Value {
        let a = self.iter().map(|v| v.to_value()).collect();
        Value::Array(a)
    }

    fn as_array(&self) -> Option<&dyn ArrayView> {
        Some(self)
    }
}

impl<T: ValueView> ArrayView for Vec<T> {
    fn as_value(&self) -> &dyn ValueView {
        self
    }

    fn size(&self) -> i64 {
        self.len() as i64
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        let i = self.as_slice().iter().map(|v| convert_value(v));
        Box::new(i)
    }

    fn contains_key(&self, index: i64) -> bool {
        let index = convert_index(index, self.size());
        index < self.size()
    }

    fn get(&self, index: i64) -> Option<&dyn ValueView> {
        let index = convert_index(index, self.size());
        let value = self.as_slice().get(index as usize);
        value.map(|v| convert_value(v))
    }
}

impl<'a, A: ArrayView + ?Sized> ArrayView for &'a A {
    fn as_value(&self) -> &dyn ValueView {
        <A as ArrayView>::as_value(self)
    }

    fn size(&self) -> i64 {
        <A as ArrayView>::size(self)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        <A as ArrayView>::values(self)
    }

    fn contains_key(&self, index: i64) -> bool {
        <A as ArrayView>::contains_key(self, index)
    }

    fn get(&self, index: i64) -> Option<&dyn ValueView> {
        <A as ArrayView>::get(self, index)
    }
}

fn convert_value(s: &dyn ValueView) -> &dyn ValueView {
    s
}

fn convert_index(index: i64, max_size: i64) -> i64 {
    if 0 <= index {
        index
    } else {
        max_size + index
    }
}

struct ArraySource<'s, T: ValueView> {
    s: &'s Vec<T>,
}

impl<'s, T: ValueView> fmt::Display for ArraySource<'s, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for item in self.s {
            write!(f, "{}, ", item.render())?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

struct ArrayRender<'s, T: ValueView> {
    s: &'s Vec<T>,
}

impl<'s, T: ValueView> fmt::Display for ArrayRender<'s, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in self.s {
            write!(f, "{}", item.render())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_array() {
        let arr = Array::new();
        println!("{}", arr.source());
        let array: &dyn ArrayView = &arr;
        println!("{}", array.source());
        let view: &dyn ValueView = array.as_value();
        println!("{}", view.source());
    }
}
