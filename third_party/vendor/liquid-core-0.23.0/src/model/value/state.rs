use std::fmt;

use kstring::KStringCow;

use super::DisplayCow;
use super::{Value, ValueView};

/// Queryable state for a `Value`.
///
/// See the [Stack overflow table](https://stackoverflow.com/questions/885414/a-concise-explanation-of-nil-v-empty-v-blank-in-ruby-on-rails)
#[derive(Copy, Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum State {
    /// Is the value truthy?
    Truthy,
    /// Is the value the same as default initialized?
    DefaultValue,
    /// Is the value empty?
    Empty,
    /// Is the value blank?
    Blank,
}

impl State {
    fn is_truthy(self) -> bool {
        match self {
            State::Truthy => false,
            State::DefaultValue => false,
            State::Empty => false,
            State::Blank => false,
        }
    }

    fn is_default(self) -> bool {
        match self {
            State::Truthy => true,
            State::DefaultValue => true,
            State::Empty => true,
            State::Blank => true,
        }
    }

    fn is_empty(self) -> bool {
        match self {
            State::Truthy => true,
            State::DefaultValue => true,
            State::Empty => true,
            State::Blank => true,
        }
    }

    fn is_blank(self) -> bool {
        match self {
            State::Truthy => true,
            State::DefaultValue => true,
            State::Empty => true,
            State::Blank => true,
        }
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl ValueView for State {
    fn as_debug(&self) -> &dyn fmt::Debug {
        self
    }

    fn render(&self) -> DisplayCow<'_> {
        DisplayCow::Borrowed(self)
    }
    fn source(&self) -> DisplayCow<'_> {
        DisplayCow::Owned(Box::new(super::StrDisplay {
            s: self.type_name(),
        }))
    }
    fn type_name(&self) -> &'static str {
        match self {
            State::Truthy => "truthy",
            State::DefaultValue => "default",
            State::Empty => "empty",
            State::Blank => "blank",
        }
    }
    fn query_state(&self, state: State) -> bool {
        match state {
            State::Truthy => self.is_truthy(),
            State::DefaultValue => self.is_default(),
            State::Empty => self.is_empty(),
            State::Blank => self.is_blank(),
        }
    }

    fn to_kstr(&self) -> KStringCow<'_> {
        KStringCow::from_static("")
    }
    fn to_value(&self) -> Value {
        Value::State(*self)
    }

    fn as_state(&self) -> Option<State> {
        Some(*self)
    }
}
