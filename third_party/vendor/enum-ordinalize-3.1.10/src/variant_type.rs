extern crate proc_macro2;

use crate::quote::{ToTokens, TokenStreamExt};

use proc_macro2::{Ident, Span, TokenStream};

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum VariantType {
    ISIZE,
    I8,
    I16,
    I32,
    I64,
    I128,
    USIZE,
    U8,
    U16,
    U32,
    U64,
    U128,
    Nondetermined,
}

impl VariantType {
    #[inline]
    pub(crate) fn from_str<S: AsRef<str>>(s: S) -> VariantType {
        let s = s.as_ref();

        match s {
            "isize" => VariantType::ISIZE,
            "i8" => VariantType::I8,
            "i16" => VariantType::I16,
            "i32" => VariantType::I32,
            "i64" => VariantType::I64,
            "i128" => VariantType::I128,
            "usize" => VariantType::USIZE,
            "u8" => VariantType::U8,
            "u16" => VariantType::U16,
            "u32" => VariantType::U32,
            "u64" => VariantType::U64,
            "u128" => VariantType::U128,
            _ => VariantType::Nondetermined,
        }
    }

    #[inline]
    pub(crate) fn as_str(&self) -> &'static str {
        match self {
            VariantType::ISIZE => "isize",
            VariantType::I8 => "i8",
            VariantType::I16 => "i16",
            VariantType::I32 => "i32",
            VariantType::I64 => "i64",
            VariantType::I128 => "i128",
            VariantType::USIZE => "usize",
            VariantType::U8 => "u8",
            VariantType::U16 => "u16",
            VariantType::U32 => "u32",
            VariantType::U64 => "u64",
            VariantType::U128 => "u128",
            _ => unreachable!(),
        }
    }
}

impl Default for VariantType {
    #[inline]
    fn default() -> Self {
        VariantType::Nondetermined
    }
}

impl ToTokens for VariantType {
    #[inline]
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Ident::new(self.as_str(), Span::call_site()));
    }
}
