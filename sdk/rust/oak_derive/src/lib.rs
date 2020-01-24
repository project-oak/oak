//
// Copyright 2019 The Project Oak Authors
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
//

//! Macro to derive standard boilerplate code for an Oak Node.

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;

/// Implements the necessary bindings to make the annotated struct act as a
/// gRPC-processing Oak Node.
///
/// May only be used on struct objects.  Assumes that the default pre-defined
/// port names (`"grpc_in"`) is used to identify the gRPC input channel.
///
/// At most one struct may be annotated with this, as it produces global symbols
/// that would otherwise conflict if implemented multiple times.
///
/// ```rust
/// use log::warn;
/// use oak::grpc::OakNode;
/// use protobuf::ProtobufEnum;
///
/// #[derive(oak_derive::OakExports)]
/// struct Node;
///
/// impl OakNode for Node {
///     fn new() -> Self {
///         Node
///     }
///     fn invoke(&mut self, method: &str, req: &[u8], writer: oak::grpc::ChannelResponseWriter) {
///         /* ... */
///     }
/// }
/// ```
#[proc_macro_derive(OakExports)]
pub fn derive_oak_exports(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = input.ident;
    match input.data {
        syn::Data::Struct(_) => (),
        _ => panic!("#[derive(OakExports)] is only defined for structs"),
    };

    let expanded = quote! {
        #[no_mangle]
        pub extern "C" fn oak_main(handle: u64) {
            // A panic in the Rust module code cannot safely pass through the FFI
            // boundary, so catch any panics here and drop them.
            // https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics
            let _ = ::std::panic::catch_unwind(||{
                ::oak::set_panic_hook();
                inner_main(handle)
            });
        }
        // Internal version of the main entrypoint, to allow testing without any
        // panic interception.
        pub fn inner_main(handle: u64) {
            let mut node = <#name>::new();
            if let ::std::result::Result::Err(s) = ::oak::grpc::event_loop(
                node,
                ::oak::ReadHandle{
                    handle: ::oak::Handle::from_raw(handle),
                },
            ) {
                ::log::warn!("Node terminating with {:?}", s);
            }
        }
    };

    TokenStream::from(expanded)
}
