//! Utility items for this crate.

use proc_macro2::*;
use std::str::FromStr;
use syn::*;

/// A wrapper around a type that only allows its value to be assigned once.
#[derive(Debug)]
pub enum AssignOnce<T> {
    Set(T),
    Unset,
}

impl<T> Default for AssignOnce<T> {
    fn default() -> Self {
        AssignOnce::Unset
    }
}

impl<T> AssignOnce<T> {
    /// Assigns `value` to `self`, however calls `err` instead if `self` is already assigned.
    pub fn set<E, F>(&mut self, value: T, err: F) -> std::result::Result<(), E>
    where
        F: FnOnce() -> E,
    {
        match self {
            AssignOnce::Set(_) => Err(err()),
            AssignOnce::Unset => {
                *self = AssignOnce::Set(value);
                Ok(())
            }
        }
    }

    /// Unwraps `self`, returning `default` if `self` is not set.
    pub fn default_to(self, default: T) -> T {
        match self {
            AssignOnce::Set(value) => value,
            AssignOnce::Unset => default,
        }
    }

    /// Converts this type to `Option`.
    pub fn into_option(self) -> Option<T> {
        match self {
            AssignOnce::Set(value) => Some(value),
            AssignOnce::Unset => None,
        }
    }

    /// Unwraps `self` or calls `err` if `self` is not set.
    pub fn unwrap_or_err<E, F>(self, err: F) -> std::result::Result<T, E>
    where
        F: FnOnce() -> E,
    {
        match self {
            AssignOnce::Set(value) => Ok(value),
            AssignOnce::Unset => Err(err()),
        }
    }
}

/// Utility function to parse `Meta::NameValue` elements that assigns a String.
pub fn assign_str_value(to: &mut AssignOnce<String>, key: &Ident, value: &Lit) -> Result<()> {
    if let Lit::Str(value) = value {
        to.set(value.value(), || {
            Error::new_spanned(key, format!("Element `{}` was already defined.", key))
        })
    } else {
        Err(Error::new_spanned(value, "Expected string literal."))
    }
}

/// Utility function to parse `Meta::NameValue` elements that assigns a value parsed from a String.
pub fn parse_str_value<T>(to: &mut AssignOnce<T>, key: &Ident, value: &Lit) -> Result<()>
where
    T: FromStr<Err = String>,
{
    if let Lit::Str(value) = value {
        let value = value
            .value()
            .parse()
            .map_err(|err| Error::new_spanned(value, err))?;
        to.set(value, || {
            Error::new_spanned(key, format!("Element `{}` was already defined.", key))
        })
    } else {
        Err(Error::new_spanned(value, "Expected string literal."))
    }
}

/// Utility function to parse `Meta::Word` elements.
pub fn assign_ident(to: &mut AssignOnce<Ident>, key: &Ident, value: Ident) -> Result<()> {
    to.set(value, || {
        Error::new_spanned(key, format!("Element `{}` was already defined.", key))
    })
}
