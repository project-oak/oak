extern crate proc_macro;
extern crate syn;

use proc_macro::TokenStream;
use quote::quote;

/// Implements the necessary bindings to make the annotated struct act as an Oak Node.
///
/// May only be used on struct objects.
///
/// At most one struct may be annotated with this, as it produces global symbols that would
/// otherwise conflict if implemented multiple times.
///
/// ```rust
/// extern crate oak;
///
/// #[derive(oak_derive::OakNode)]
/// struct Node;
///
/// impl oak::Node for Node {
///     fn new() -> Self { Node }
///     fn invoke(&mut self, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) { /* ... */ }
/// }
/// ```
#[proc_macro_derive(OakNode)]
pub fn derive_oak_node(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = input.ident;
    match input.data {
        syn::Data::Struct(_) => (),
        _ => panic!("#[derive(OakNode)] is only defined for structs"),
    };

    let expanded = quote! {
        #[no_mangle]
        pub extern "C" fn oak_initialize() {
            oak::set_node::<#name>();
        }
    };

    TokenStream::from(expanded)
}
