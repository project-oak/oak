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
/// extern crate oak;
/// extern crate protobuf;
/// use oak::grpc::OakNode;
/// use protobuf::ProtobufEnum;
///
/// #[derive(oak_derive::OakExports)]
/// struct Node;
///
/// impl OakNode for Node {
///     fn new() -> Self { Node }
///     fn invoke(&mut self, method: &str, req: &[u8], writer: oak::grpc::ChannelResponseWriter) { /* ... */ }
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
        pub extern "C" fn oak_main() -> i32 {
            // A panic in the Rust module code cannot safely pass through the FFI
            // boundary, so catch any panics here and translate to an error return.
            // https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics
            match std::panic::catch_unwind(||{
                let mut node = <#name>::new();
                oak::grpc::event_loop(node, oak::ReadHandle{ handle: oak::channel_find(oak::grpc::DEFAULT_IN_PORT_NAME) })
            }) {
                Ok(rc) => rc,
                Err(_) => oak::OakStatus::ERR_INTERNAL.value(),
            }
        }
    };

    TokenStream::from(expanded)
}
