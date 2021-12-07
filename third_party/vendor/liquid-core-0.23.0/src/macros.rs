/// A value::Value literal.
///
/// # Example
///
/// ```rust
/// # use liquid_core::model::ValueView;
/// #
/// # fn main() {
/// liquid_core::value!(5)
///     .as_scalar().unwrap()
///     .to_integer().unwrap();
/// liquid_core::value!("foo")
///     .as_scalar().unwrap()
///     .to_kstr();
/// liquid_core::value!([1, "2", 3])
///     .as_array().unwrap();
/// liquid_core::value!({"foo": 5})
///     .as_object().unwrap();
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! value {
    ($($value:tt)+) => {
        value_internal!($($value)+)
    };
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! value_internal {
    //////////////////////////////////////////////////////////////////////////
    // The main implementation.
    //
    // Must be invoked as: value_internal!($($value)+)
    //////////////////////////////////////////////////////////////////////////

    (nil) => {
        $crate::model::Value::Nil
    };

    (true) => {
        $crate::model::Value::scalar(true)
    };

    (false) => {
        $crate::model::Value::scalar(false)
    };

    ([]) => {
        $crate::model::Value::Array(::std::default::Default::default())
    };

    ([ $($tt:tt)+ ]) => {
        $crate::model::Value::Array(array_internal!(@array [] $($tt)+))
    };

    ({}) => {
        $crate::model::Value::Object(::std::default::Default::default())
    };

    ({ $($tt:tt)+ }) => {
        $crate::model::Value::Object({
            let mut object = $crate::model::Object::new();
            object_internal!(@object object () ($($tt)+) ($($tt)+));
            object
        })
    };

    ($other:ident) => {
        $other
    };

    // Any Serialize type: numbers, strings, struct literals, variables etc.
    // Must be below every other rule.
    ($other:expr) => {
        $crate::model::to_value(&$other).unwrap()
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! value_unexpected {
    () => {};
}

/// A value::Object literal.
///
/// # Example
///
/// ```rust
/// # fn main() {
/// liquid_core::object!({"foo": 5});
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! object {
    ($($value:tt)+) => {
        object_internal!($($value)+)
    };
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! object_internal {
    //////////////////////////////////////////////////////////////////////////
    // TT muncher for parsing the inside of an object {...}. Each entry is
    // inserted into the given map variable.
    //
    // Must be invoked as: object_internal!(@object $object () ($($tt)*) ($($tt)*))
    //
    // We require two copies of the input tokens so that we can match on one
    // copy and trigger errors on the other copy.
    //////////////////////////////////////////////////////////////////////////

    // Done.
    (@object $object:ident () () ()) => {};

    // Insert the current entry followed by trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr) , $($rest:tt)*) => {
        let _ = $object.insert(($($key)+).into(), $value);
        object_internal!(@object $object () ($($rest)*) ($($rest)*));
    };

    // Current entry followed by unexpected token.
    (@object $object:ident [$($key:tt)+] ($value:expr) $unexpected:tt $($rest:tt)*) => {
        object_unexpected!($unexpected);
    };

    // Insert the last entry without trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr)) => {
        let _ = $object.insert(($($key)+).into(), $value);
    };

    // Next value is `nil`.
    (@object $object:ident ($($key:tt)+) (: nil $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!(nil)) $($rest)*);
    };

    // Next value is `true`.
    (@object $object:ident ($($key:tt)+) (: true $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!(true)) $($rest)*);
    };

    // Next value is `false`.
    (@object $object:ident ($($key:tt)+) (: false $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!(false)) $($rest)*);
    };

    // Next value is an array.
    (@object $object:ident ($($key:tt)+) (: [$($array:tt)*] $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!([$($array)*])) $($rest)*);
    };

    // Next value is a map.
    (@object $object:ident ($($key:tt)+) (: {$($map:tt)*} $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!({$($map)*})) $($rest)*);
    };

    // Next value is an expression followed by comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr , $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!($value)) , $($rest)*);
    };

    // Last value is an expression with no trailing comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr) $copy:tt) => {
        object_internal!(@object $object [$($key)+] (value_internal!($value)));
    };

    // Missing value for last entry. Trigger a reasonable error message.
    (@object $object:ident ($($key:tt)+) (:) $copy:tt) => {
        // "unexpected end of macro invocation"
        object_internal!();
    };

    // Missing colon and value for last entry. Trigger a reasonable error
    // message.
    (@object $object:ident ($($key:tt)+) () $copy:tt) => {
        // "unexpected end of macro invocation"
        object_internal!();
    };

    // Misplaced colon. Trigger a reasonable error message.
    (@object $object:ident () (: $($rest:tt)*) ($colon:tt $($copy:tt)*)) => {
        // Takes no arguments so "no rules expected the token `:`".
        object_unexpected!($colon);
    };

    // Found a comma inside a key. Trigger a reasonable error message.
    (@object $object:ident ($($key:tt)*) (, $($rest:tt)*) ($comma:tt $($copy:tt)*)) => {
        // Takes no arguments so "no rules expected the token `,`".
        object_unexpected!($comma);
    };

    // Key is fully parenthesized. This avoids clippy double_parens false
    // positives because the parenthesization may be necessary here.
    (@object $object:ident () (($key:expr) : $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object ($key) (: $($rest)*) (: $($rest)*));
    };

    // Munch a token into the current key.
    (@object $object:ident ($($key:tt)*) ($tt:tt $($rest:tt)*) $copy:tt) => {
        object_internal!(@object $object ($($key)* $tt) ($($rest)*) ($($rest)*));
    };

    //////////////////////////////////////////////////////////////////////////
    // The main implementation.
    //
    // Must be invoked as: object_internal!($($value)+)
    //////////////////////////////////////////////////////////////////////////

    ({}) => {
        $crate::model::Object::new()
    };

    ({ $($tt:tt)+ }) => {
        {
            let mut object = $crate::model::Object::new();
            object_internal!(@object object () ($($tt)+) ($($tt)+));
            object
        }
    };

    ($other:ident) => {
        $other
    };

    // Any Serialize type: numbers, strings, struct literals, variables etc.
    // Must be below every other rule.
    ($other:expr) => {
        $crate::model::to_object(&$other).unwrap()
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! object_unexpected {
    () => {};
}

/// A value::Array literal.
///
/// # Example
///
/// ```rust
/// # use liquid_core::model::ValueView;
/// #
/// # fn main() {
/// liquid_core::array!([1, "2", 3]);
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! array {
    ($($value:tt)+) => {
        array_internal!($($value)+)
    };
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! array_internal {
    // Done with trailing comma.
    (@array [$($elems:expr,)*]) => {
        array_internal_vec![$($elems,)*]
    };

    // Done without trailing comma.
    (@array [$($elems:expr),*]) => {
        array_internal_vec![$($elems),*]
    };

    // Next element is `nil`.
    (@array [$($elems:expr,)*] nil $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!(nil)] $($rest)*)
    };

    // Next element is `true`.
    (@array [$($elems:expr,)*] true $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!(true)] $($rest)*)
    };

    // Next element is `false`.
    (@array [$($elems:expr,)*] false $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!(false)] $($rest)*)
    };

    // Next element is an array.
    (@array [$($elems:expr,)*] [$($array:tt)*] $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!([$($array)*])] $($rest)*)
    };

    // Next element is a map.
    (@array [$($elems:expr,)*] {$($map:tt)*} $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!({$($map)*})] $($rest)*)
    };

    // Next element is an expression followed by comma.
    (@array [$($elems:expr,)*] $next:expr, $($rest:tt)*) => {
        array_internal!(@array [$($elems,)* value_internal!($next),] $($rest)*)
    };

    // Last element is an expression with no trailing comma.
    (@array [$($elems:expr,)*] $last:expr) => {
        array_internal!(@array [$($elems,)* value_internal!($last)])
    };

    // Comma after the most recent element.
    (@array [$($elems:expr),*] , $($rest:tt)*) => {
        array_internal!(@array [$($elems,)*] $($rest)*)
    };

    // Unexpected token after most recent element.
    (@array [$($elems:expr),*] $unexpected:tt $($rest:tt)*) => {
        array_unexpected!($unexpected)
    };

    //////////////////////////////////////////////////////////////////////////
    // The main implementation.
    //
    // Must be invoked as: value_internal!($($value)+)
    //////////////////////////////////////////////////////////////////////////

    ([]) => {
        $crate::model::Array::default()
    };

    ([ $($tt:tt)+ ]) => {
        array_internal!(@array [] $($tt)+)
    };

    ($other:ident) => {
        $other
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! array_internal_vec {
    ($($content:tt)*) => {
        vec![$($content)*]
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! array_unexpected {
    () => {};
}

/// A value::Scalar literal.
///
/// # Example
///
/// ```rust
/// # use liquid_core::model::ValueView;
/// #
/// # fn main() {
/// liquid_core::scalar!(5)
///     .to_integer().unwrap();
/// liquid_core::scalar!("foo")
///     .to_kstr();
/// # }
/// ```
#[macro_export]
macro_rules! scalar {
    ($value:literal) => {
        $crate::model::Scalar::new($value)
    };

    ($other:ident) => {
        $other
    };

    // Any Serialize type: numbers, strings, struct literals, variables etc.
    // Must be below every other rule.
    ($other:expr) => {
        $crate::model::to_scalar(&$other).unwrap()
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! call_filter {
    ($filter:expr, $input:expr) => {{
        $crate::call_filter!($filter, $input, )
    }};
    ($filter:expr, $input:expr, $($args:expr),*) => {{
        let positional = Box::new(vec![$($crate::Expression::Literal($crate::value!($args))),*].into_iter());
        let keyword = Box::new(Vec::new().into_iter());
        let args = $crate::parser::FilterArguments { positional, keyword };

        let runtime = $crate::runtime::RuntimeBuilder::new().build();

        let input = $crate::value!($input);

        $crate::ParseFilter::parse(&$filter, args)
            .and_then(|filter| $crate::Filter::evaluate(&*filter, &input, &runtime))
    }};
}
