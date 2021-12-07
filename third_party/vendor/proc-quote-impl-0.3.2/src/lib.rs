//! This is the proc-macro part of the proc-quote crate.
//! Do not use this crate directly.

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;

mod proc_quote;

#[doc(hidden)]
#[proc_macro_hack]
pub fn quote(input: TokenStream) -> TokenStream {
    proc_quote::quote(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_hack]
pub fn quote_spanned(input: TokenStream) -> TokenStream {
    proc_quote::quote_spanned(input.into()).into()
}
