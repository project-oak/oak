//! Key String: Optimized for map keys.
//!
//! # Background
//!
//! Considerations:
//! - Large maps
//! - Most keys live and drop without being used in any other way
//! - Most keys are relatively small (single to double digit bytes)
//! - Keys are immutable
//! - Allow zero-cost abstractions between structs and maps (e.g. no allocating
//!   when dealing with struct field names)
//!
//! Ramifications:
//! - Inline small strings rather than going to the heap.
//! - Preserve `&'static str` across strings (`KString`),
//!   references (`KStringRef`), and lifetime abstractions (`KStringCow`) to avoid
//!   allocating for struct field names.
//! - Use `Box<str>` rather than `String` to use less memory.

mod cow;
mod inline;
mod r#ref;
mod string;

pub use cow::*;
pub use r#ref::*;
pub use string::*;

#[cfg(test)]
mod test {
    #[test]
    fn test_size() {
        println!(
            "String: {}",
            std::mem::size_of::<crate::string::StdString>()
        );
        println!(
            "Box<str>: {}",
            std::mem::size_of::<crate::string::OwnedStr>()
        );
        println!(
            "Box<Box<str>>: {}",
            std::mem::size_of::<Box<crate::string::OwnedStr>>()
        );
        println!("str: {}", std::mem::size_of::<&'static str>());
        println!(
            "Cow: {}",
            std::mem::size_of::<std::borrow::Cow<'static, str>>()
        );
    }
}
