//
// Copyright 2020 The Project Oak Authors
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

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Returns a [`TokenStream`] representing the specified Rust type.
///
/// This is necessary because in most cases the type will be a generated protobuf struct, but for
/// instance the `Empty` protobuf is represented as `()` by prost, which is not a valid identifier.
fn type_ident(type_: &str) -> TokenStream {
    if type_ == "()" {
        quote!(())
    } else {
        let t = format_ident!("{}", type_);
        quote!(#t)
    }
}

/// Returns the name to use to refer to the `oak` package.
///
/// When compiling from within the `oak` crate we need to use `crate` to refer to itself.
fn oak_package() -> TokenStream {
    if std::env::var("CARGO_PKG_NAME").unwrap() == "oak" {
        quote!(crate)
    } else {
        quote!(::oak)
    }
}

struct OakServiceGenerator;

impl prost_build::ServiceGenerator for OakServiceGenerator {
    fn generate(&mut self, service: prost_build::Service, out: &mut std::string::String) {
        let oak_package = oak_package();

        let service_name = format_ident!("{}", service.name);
        let service_methods = service.methods.iter().map(|method| {
            let method_name = format_ident!("{}", method.name);
            let input_type = type_ident(&method.input_type);
            let output_type = type_ident(&method.output_type);
            // TODO(#97): Better client-side streaming.
            match (method.client_streaming, method.server_streaming) {
                (false, false) => quote! {
                    fn #method_name(&mut self, req: #input_type) -> #oak_package::grpc::Result<#output_type>
                },
                (false, true) => quote! {
                    fn #method_name(&mut self, req: #input_type, writer: #oak_package::grpc::ChannelResponseWriter)
                },
                (true, false) => quote! {
                    fn #method_name(&mut self, reqs: Vec<#input_type>) -> #oak_package::grpc::Result<#output_type>
                },
                (true, true) => quote! {
                    fn #method_name(&mut self, reqs: Vec<#input_type>, writer: #oak_package::grpc::ChannelResponseWriter)
                },
            }
        });

        let dispatcher_name = format_ident!("{}Dispatcher", service.name);
        let dispatcher_methods = service.methods.iter().map(|method| {
            let method_name = format_ident!("{}", method.name);
            let method_name_string = format!("/{}.{}/{}", service.package, service.proto_name, method.proto_name);
            // Figure out which generic function applies.
            let handle_invocation = match (method.client_streaming, method.server_streaming) {
                (false, false) => quote! {
                    #oak_package::grpc::handle_req_rsp(|r| (self.0).#method_name(r), req, writer)
                },
                (false, true) => quote! {
                    #oak_package::grpc::handle_req_stream(|r, w| (self.0).#method_name(r, w), req, writer)
                },
                (true, false) => quote! {
                    #oak_package::grpc::handle_stream_rsp(|rr| (self.0).#method_name(rr), req, writer)
                },
                (true, true) => quote! {
                    #oak_package::grpc::handle_stream_stream(|rr, w| (self.0).#method_name(rr, w), req, writer)
                },
            };
            quote! {
                #method_name_string => #handle_invocation
            }
        });

        let client_name = format_ident!("{}Client", service.name);
        let client_methods = service.methods.iter().map(|method| {
            let method_name = format_ident!("{}", method.name);
            let input_type = type_ident(&method.input_type);
            let output_type = type_ident(&method.output_type);
            let method_name_string = format!("/{}.{}/{}", service.package, service.proto_name, method.proto_name);
            // TODO(#97): Support client-side streaming.
            #[allow(clippy::match_bool)]
            match method.server_streaming {
                false =>
                    quote! {
                        pub fn #method_name(&self, req: #input_type) -> #oak_package::grpc::Result<#output_type> {
                            #oak_package::grpc::invoke_grpc_method(#method_name_string, &req, &self.0.invocation_sender)
                        }
                    },
                true =>
                    // TODO(#592): ideally the return type for a streaming method would be
                    //   format!("oak::io::Receiver<{}>", self.output_message());
                    // This is not possible with the current io::Receiver's direct use of
                    // the underlying handle.
                    quote! {
                        pub fn #method_name(&self, req: #input_type) -> #oak_package::grpc::Result<#oak_package::io::Receiver<#oak_package::grpc::GrpcResponse>> {
                            #oak_package::grpc::invoke_grpc_method_stream(#method_name_string, &req, &self.0.invocation_sender)
                        }
                    },
            }
        });
        let gen = quote! {
            pub trait #service_name {
                #(#service_methods;)*
            }

            #[allow(dead_code)]
            pub struct #dispatcher_name<T: #service_name>(T);

            #[allow(dead_code)]
            impl <T: #service_name> #dispatcher_name<T> {
                pub fn new(node: T) -> #dispatcher_name<T> {
                    #dispatcher_name(node)
                }
            }

            #[allow(clippy::unit_arg)]
            impl <T: #service_name> #oak_package::grpc::ServerNode for #dispatcher_name<T> {
                fn invoke(&mut self, method: &str, req: &[u8], writer: #oak_package::grpc::ChannelResponseWriter) {
                    match method {
                        #(#dispatcher_methods,)*
                        _ => {
                            ::log::error!("unknown method name: {}", method);
                        }
                    }
                }
            }

            #[allow(dead_code)]
            pub struct #client_name(pub #oak_package::grpc::client::Client);

            #[allow(dead_code)]
            impl #client_name {
                #(#client_methods)*
            }
        };
        out.push_str("\n");
        // TODO(#832): Currently the generated output is squashed on a single line; consider passing
        // it through rustfmt, if it does not increase compile time too much.
        out.push_str(&format!("{}", gen));
        out.push_str("\n");
    }
}

/// Build Rust code corresponding to a set of protocol buffer message and service definitions,
/// emitting generated code to crate's `OUT_DIR`.  For gRPC service definitions, this
/// function generates Oak-specific code that is suitable for use inside an Oak Node (i.e.  *not*
/// code that is suitable for use in a normal application running on the host platform).
pub fn compile_protos<P>(inputs: &[P], includes: &[P])
where
    P: AsRef<std::path::Path>,
{
    compile_protos_with(true, inputs, includes);
}

/// Build Rust code corresponding to a set of protocol buffer messages, skipping any service
/// definitions, emitting generated code to crate's `OUT_DIR`.
pub fn compile_protos_without_services<P>(inputs: &[P], includes: &[P])
where
    P: AsRef<std::path::Path>,
{
    compile_protos_with(false, inputs, includes);
}

fn compile_protos_with<P>(generate_services: bool, inputs: &[P], includes: &[P])
where
    P: AsRef<std::path::Path>,
{
    for input in inputs {
        // Tell cargo to rerun this build script if the proto file has changed.
        // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
        println!("cargo:rerun-if-changed={}", input.as_ref().display());
    }

    let mut prost_config = prost_build::Config::new();
    if generate_services {
        prost_config.service_generator(Box::new(OakServiceGenerator));
    }
    prost_config
        // We require label-related types to be comparable and hashable so that they can be used in
        // hash-based collections.
        .type_attribute(".oak.label", "#[derive(Eq, Hash)]")
        .compile_protos(inputs, includes)
        .expect("could not run prost-build");
}

/// Generate Protobuf code using `tonic`.
/// `build_client` and `build_server` specify whether to generate client or server related code.
fn compile_proto(
    proto_path: &str,
    file_path: &str,
    build_client: bool,
    build_server: bool,
) -> std::io::Result<()> {
    // TODO(#1093): Move all proto generation to a common crate.
    let proto_path = std::path::Path::new(proto_path);
    let file_path = proto_path.join(file_path);

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    println!("cargo:rerun-if-changed={}", file_path.display());

    // Generate the normal (non-Oak) server and client code for the gRPC service,
    // along with the Rust types corresponding to the message definitions.
    tonic_build::configure()
        .build_client(build_client)
        .build_server(build_server)
        .compile(&[file_path.as_path()], &[proto_path])
}

/// Generate Protobuf code for client using `tonic`.
pub fn compile_client_proto(proto_path: &str, file_path: &str) -> std::io::Result<()> {
    compile_proto(proto_path, file_path, true, false)
}

/// Generate Protobuf code for server using `tonic`.
pub fn compile_server_proto(proto_path: &str, file_path: &str) -> std::io::Result<()> {
    compile_proto(proto_path, file_path, false, true)
}
