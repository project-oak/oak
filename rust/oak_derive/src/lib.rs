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
///     fn invoke(&mut self, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) { /* ... */ }
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
        pub extern "C" fn oak_initialize() -> i32{
            // A panic in the Rust module code cannot safely pass through the FFI
            // boundary, so catch any panics here and translate to an error return.
            // https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics
            match std::panic::catch_unwind(||{
                oak::set_node::<#name>();
            }) {
                Ok(_) => oak::raw_status(oak::Status::Ok),
                Err(_) => oak::raw_status(oak::Status::InternalError),
            }
        }
    };

    TokenStream::from(expanded)
}
