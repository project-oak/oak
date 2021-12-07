pub use liquid_core::Value::Nil;

#[allow(dead_code)]
pub fn date(y: i32, m: u32, d: u32) -> liquid_core::Value {
    use liquid_core::model::Date;
    use liquid_core::model::Value;
    Value::scalar(Date::from_ymd(y, m, d))
}

#[allow(dead_code)]
pub fn with_time(_time: &str) -> liquid_core::Value {
    Nil
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! v {
    ($($value:tt)+) => {
        ::liquid_core::value!($($value)+)
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! o {
    ($($value:tt)+) => {
        ::liquid_core::object!($($value)+)
    };
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! a {
    ($($value:tt)+) => {
        ::liquid_core::array!($($value)+)
    };
}
