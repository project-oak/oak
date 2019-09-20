// Simple equality test macro that returns an Err value on mismatch.
// Adapted from standard library assert_eq! macro.
#[macro_export]
macro_rules! expect_eq {
    ($left:expr, $right:expr) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::Other,
                        format!(
                            r#"{}:{}: expectation failed: `(left == right)`
  left: `{:?}`,
 right: `{:?}`"#,
                            file!(),
                            line!(),
                            &*left_val,
                            &*right_val
                        ),
                    ));
                }
            }
        }
    }};
}

// Check if an expression matches a pattern, and generate an Err value if not.
// Adapted from https://github.com/murarth/assert_matches.
#[macro_export]
macro_rules! expect_matches {
    ( $e:expr , $pat:pat ) => {
        match $e {
            $pat => (),
            ref e => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!(
                        "{}:{}: expectation failed: `{:?}` does not match `{}`",
                        file!(),
                        line!(),
                        e,
                        stringify!($pat)
                    ),
                ));
            }
        }
    };
}

#[macro_export]
macro_rules! expect {
    ( $e:expr ) => {
        if !$e {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!(
                    "{}:{}: expectation failed: {:?} is false",
                    file!(),
                    line!(),
                    stringify!($e)
                ),
            ));
        }
    };
}
