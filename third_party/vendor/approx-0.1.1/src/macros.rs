// Copyright 2015 Brendan Zabarauskas
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// Predicate for testing the approximate equality of two values.
#[macro_export]
macro_rules! relative_eq {
    ($lhs:expr, $rhs:expr, $($opt:ident = $opt_val:expr),+) => {{
        $crate::Relative::new(&$lhs, &$rhs)$(.$opt($opt_val))+.eq()
    }};
    ($lhs:expr, $rhs:expr) => {{
        $crate::Relative::new(&$lhs, &$rhs).eq()
    }};
}

/// Predicate for testing the approximate inequality of two values.
#[macro_export]
macro_rules! relative_ne {
    ($lhs:expr, $rhs:expr, $($opt:ident = $opt_val:expr),+) => {{
        $crate::Relative::new(&$lhs, &$rhs)$(.$opt($opt_val))+.ne()
    }};
    ($lhs:expr, $rhs:expr) => {{
        $crate::Relative::new(&$lhs, &$rhs).ne()
    }};
}

#[macro_export]
macro_rules! assert_relative_eq {
    ($given:expr, $expected:expr) => {{
        let (given, expected) = (&($given), &($expected));

        if !relative_eq!(given, expected) {
            panic!(
"assert_relative_eq!({}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr),+) => {{
        let (given, expected) = (&($given), &($expected));

        if !relative_eq!(given, expected, $($opt = $opt_val),+) {
            panic!(
"assert_relative_eq!({}, {}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                stringify!($($opt = $opt_val),+),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr,) => {
        assert_relative_eq!($given, $expected)
    };
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr,)+) => {
        assert_relative_eq!($given, $expected, $($opt = $opt_val),+)
    };
}

#[macro_export]
macro_rules! assert_relative_ne {
    ($given:expr, $expected:expr) => {{
        let (given, expected) = (&($given), &($expected));

        if !relative_ne!(given, expected) {
            panic!(
"assert_relative_ne!({}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr),+) => {{
        let (given, expected) = (&($given), &($expected));

        if !relative_ne!(given, expected, $($opt = $opt_val),+) {
            panic!(
"assert_relative_ne!({}, {}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                stringify!($($opt = $opt_val),+),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr,) => {
        assert_relative_ne!($given, $expected)
    };
}


/// Predicate for testing the approximate equality of two values using a maximum ULPs (Units
/// in Last Place).
#[macro_export]
macro_rules! ulps_eq {
    ($lhs:expr, $rhs:expr, $($opt:ident = $opt_val:expr),+) => {{
        $crate::Ulps::new(&$lhs, &$rhs)$(.$opt($opt_val))+.eq()
    }};
    ($lhs:expr, $rhs:expr) => {{
        $crate::Ulps::new(&$lhs, &$rhs).eq()
    }};
}

/// Predicate for testing the approximate inequality of two values using a maximum ULPs (Units
/// in Last Place).
#[macro_export]
macro_rules! ulps_ne {
    ($lhs:expr, $rhs:expr, $($opt:ident = $opt_val:expr),+) => {{
        $crate::Ulps::new(&$lhs, &$rhs)$(.$opt($opt_val))+.ne()
    }};
    ($lhs:expr, $rhs:expr) => {{
        $crate::Ulps::new(&$lhs, &$rhs).ne()
    }};
}

#[macro_export]
macro_rules! assert_ulps_eq {
    ($given:expr, $expected:expr) => {{
        let (given, expected) = (&($given), &($expected));

        if !ulps_eq!(given, expected) {
            panic!(
"assert_ulps_eq!({}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr),+) => {{
        let (given, expected) = (&($given), &($expected));

        if !ulps_eq!(given, expected, $($opt = $opt_val),+) {
            panic!(
"assert_ulps_eq!({}, {}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                stringify!($($opt = $opt_val),+),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr,) => {
        assert_ulps_eq!($given, $expected)
    };
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr,)+) => {
        assert_ulps_eq!($given, $expected, $($opt = $opt_val),+)
    };
}

#[macro_export]
macro_rules! assert_ulps_ne {
    ($given:expr, $expected:expr) => {{
        let (given, expected) = (&($given), &($expected));

        if !ulps_ne!(given, expected) {
            panic!(
"assert_ulps_ne!({}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr, $($opt:ident = $opt_val:expr),+) => {{
        let (given, expected) = (&($given), &($expected));

        if !ulps_ne!(given, expected, $($opt = $opt_val),+) {
            panic!(
"assert_ulps_ne!({}, {}, {})

    left = {:?}
    right = {:?}

",
                stringify!($given), stringify!($expected),
                stringify!($($opt = $opt_val),+),
                given, expected,
            );
        }
    }};
    ($given:expr, $expected:expr,) => {
        assert_ulps_ne!($given, $expected)
    };
}
