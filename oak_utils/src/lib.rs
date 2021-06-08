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

use proc_macro2::{Ident, TokenStream};
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
        let dispatcher_invocable_methods = service.methods.iter().map(|method| {
            let method_name = format_ident!("{}", method.name);
            let method_name_string = format!(
                "/{}.{}/{}",
                service.package, service.proto_name, method.proto_name
            );
            // Figure out which `ServerMethod` variant applies.
            let invocable_method = match (method.client_streaming, method.server_streaming) {
                (false, false) => quote! {
                    Some(&#oak_package::grpc::ServerMethod::UnaryUnary(T::#method_name))
                },
                (false, true) => quote! {
                    // The response type is not actually used in the method signature, so we need to manually specify a placeholder.
                    Some(&#oak_package::grpc::ServerMethod::<_, _, ()>::UnaryStream(T::#method_name))
                },
                (true, false) => quote! {
                    Some(&#oak_package::grpc::ServerMethod::StreamUnary(T::#method_name))
                },
                (true, true) => quote! {
                    // The response type is not actually used in the method signature, so we need to manually specify a placeholder.
                    Some(&#oak_package::grpc::ServerMethod::<_, _, ()>::StreamStream(T::#method_name))
                },
            };
            quote! {
                #method_name_string => #invocable_method
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
                            #oak_package::grpc::invoke_grpc_method(#method_name_string, &req, &self.0)
                        }
                    },
                true =>
                    // TODO(#592): ideally the return type for a streaming method would be
                    //   format!("oak::io::Receiver<{}>", self.output_message());
                    // This is not possible with the current io::Receiver's direct use of
                    // the underlying handle.
                    quote! {
                        pub fn #method_name(&self, req: #input_type) -> #oak_package::grpc::Result<#oak_package::io::Receiver<#oak_package::grpc::GrpcResponse>> {
                            #oak_package::grpc::invoke_grpc_method_stream(#method_name_string, &req, &self.0)
                        }
                    },
            }
        });
        let gen = quote! {
            pub trait #service_name {
                #(#service_methods;)*
            }

            #[allow(dead_code)]
            pub struct #dispatcher_name;

            #[allow(dead_code)]
            impl #dispatcher_name {
                pub fn server_method<T: #service_name>(method_name: &str) -> Option<&dyn #oak_package::grpc::Invocable<T>> {
                    match method_name {
                        #(#dispatcher_invocable_methods,)*
                        _ => None
                    }
                }
            }

            #[allow(dead_code)]
            pub struct #client_name(pub #oak_package::io::Sender<#oak_package::grpc::Invocation>);

            #[allow(dead_code)]
            impl #client_name {
                #(#client_methods)*
            }
        };
        out.push('\n');
        // TODO(#832): Currently the generated output is squashed on a single line; consider passing
        // it through rustfmt, if it does not increase compile time too much.
        out.push_str(&format!("{}", gen));
        out.push('\n');
    }
}

struct AsyncServiceGenerator;

impl prost_build::ServiceGenerator for AsyncServiceGenerator {
    fn generate(&mut self, service: prost_build::Service, out: &mut String) {
        let oak_package = oak_package();
        let name = format_ident!("{}", service.name);
        let service_enum = generate_service_enum(&name, &service);

        let method_matchers = service.methods.iter().map(|method| {
            let method_name = format_ident!("{}", method.proto_name);
            let variant = quote!(#name::#method_name);
            let input_type = type_ident(&method.input_type);
            let input = if method.client_streaming {
                quote!(requests.into_type::<#input_type>())
            } else {
                quote!(requests.into_type::<#input_type>().first().await?)
            };
            let writer = if method.server_streaming {
                quote!(MultiWriter)
            } else {
                quote!(OneshotWriter)
            };
            let output = quote!(oak_async::grpc::#writer::new(response_writer));
            let return_expr = quote!(#variant(#input, #output));
            let method_name_string = format!(
                "/{}.{}/{}",
                service.package, service.proto_name, method.proto_name
            );
            quote! {
                #method_name_string => Ok(#return_expr),
            }
        });
        let service_enum_impl = quote! {
            impl #name {
                #[allow(dead_code)]
                pub async fn from_invocation(invocation: #oak_package::grpc::Invocation) -> Result<#name, #oak_package::OakError> {
                    let ::oak_async::grpc::DecomposedInvocation { method, requests, response_writer } =
                    ::oak_async::grpc::DecomposedInvocation::from(invocation).await?;
                    match method.as_str() {
                        #(#method_matchers)*
                        _ => {
                            ::log::error!("unknown method name: {}", method);
                            Err(#oak_package::OakStatus::ErrInvalidArgs.into())
                        }
                    }
                }
            }
        };

        let gen = quote! {
            pub mod asynchronous {
                use super::*;
                #service_enum

                #service_enum_impl
            }
        };
        out.push_str(&format!("{}", gen));
        out.push('\n');

        // Eventually the sync code generation will be removed, but until then we also generate that
        // code.
        OakServiceGenerator.generate(service, out);
    }
}

fn generate_service_enum(enum_name: &Ident, service: &prost_build::Service) -> TokenStream {
    let variants = service.methods.iter().map(|method| {
        let variant = format_ident!("{}", method.proto_name);
        let input_type = type_ident(&method.input_type);
        let output_type = type_ident(&method.output_type);
        let input_type = if method.client_streaming {
            quote!(::oak_async::ChannelReadStream<#input_type>)
        } else {
            quote!(#input_type)
        };
        let output_type = if method.server_streaming {
            quote!(::oak_async::grpc::MultiWriter<#output_type>)
        } else {
            quote!(::oak_async::grpc::OneshotWriter<#output_type>)
        };
        quote!(#variant(#input_type, #output_type))
    });

    quote! {
        #[allow(dead_code)]
        pub enum #enum_name {
            #(#variants,)*
        }
    }
}

/// Options for generating Protocol buffer Rust types.
pub struct ProtoOptions {
    /// Generate Oak-specific service code for inter-node communication.
    ///
    /// Default: **true**.
    ///
    /// Generated code depends on the `oak` SDK crate.
    pub generate_services: bool,

    /// Automatically derive the `HandleVisit` trait from the Oak SDK for generated Protobuf types.
    /// If this is enabled, the generated types can contain handles and can be used to exchange
    /// handles with other nodes using inter-node communication over Protocol Buffers.
    ///
    /// Default: **true**.
    ///
    /// Generated code depends on the `oak` SDK crate.
    pub derive_handle_visit: bool,

    /// Enable service code generated for the async SDK.
    ///
    /// Default: **false**.
    ///
    /// The regular sync code will still be generated if this is enabled.
    ///
    /// This feature is currently experimental.
    pub experimental_async: bool,

    pub out_dir_override: Option<std::path::PathBuf>,
}

/// The default option values.
impl Default for ProtoOptions {
    fn default() -> ProtoOptions {
        ProtoOptions {
            generate_services: true,
            derive_handle_visit: true,
            experimental_async: false,
            out_dir_override: None,
        }
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
    compile_protos_with_options(inputs, includes, ProtoOptions::default());
}

/// Like `compile_protos`, but allows for configuring options through `ProtoOptions`.
pub fn compile_protos_with_options<P>(inputs: &[P], includes: &[P], options: ProtoOptions)
where
    P: AsRef<std::path::Path>,
{
    set_protoc_env_if_unset();

    for input in inputs {
        // Tell cargo to rerun this build script if the proto file has changed.
        // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
        println!("cargo:rerun-if-changed={}", input.as_ref().display());
    }

    let mut prost_config = prost_build::Config::new();
    if options.generate_services {
        if options.experimental_async {
            // AsyncServiceGenerator calls OakServiceGenerator, so the sync code is either way.
            prost_config.service_generator(Box::new(AsyncServiceGenerator));
        } else {
            prost_config.service_generator(Box::new(OakServiceGenerator));
        }
    }
    if options.derive_handle_visit {
        prost_config
            // Auto-derive the HandleVisit trait
            .type_attribute(".", "#[derive(::oak_io::handle::HandleVisit)]")
            // Link relevant Oak protos to the appropriate oak_io and oak_services types.
            .extern_path(".oak.handle", "::oak_io::handle")
            .extern_path(".oak.encap", "::oak_services::proto::oak::encap");
    }
    if let Some(out_dir) = options.out_dir_override {
        prost_config.out_dir(out_dir);
    }
    prost_config
        // We require identity-related types to be serializable and deserializable to and from JSON.
        .type_attribute(
            ".oak.identity",
            "#[derive(serde::Deserialize, serde::Serialize)]",
        )
        .type_attribute(".oak.identity", "#[serde(rename_all = \"camelCase\")]");
    prost_config
        // We require label-related types to be comparable and hashable so that they can be used in
        // hash-based collections.
        .type_attribute(".oak.label", "#[derive(Eq, Hash)]")
        .type_attribute(
            ".oak.label",
            "#[derive(serde::Deserialize, serde::Serialize)]",
        )
        .type_attribute(".oak.label", "#[serde(rename_all = \"camelCase\")]")
        .compile_protos(inputs, includes)
        .expect("could not run prost-build");
}

/// Options for building gRPC code.
#[derive(Default)]
pub struct CodegenOptions {
    /// Specify whether to build client related code.
    pub build_client: bool,
    /// Specify whether to build server related code.
    pub build_server: bool,
    /// Specify externally provided Protobuf packages or types.
    pub extern_paths: Vec<ExternPath>,
}

#[derive(Default)]
pub struct ExternPath {
    proto_path: String,
    rust_path: String,
}

impl ExternPath {
    pub fn new(proto_path: &str, rust_path: &str) -> Self {
        ExternPath {
            proto_path: proto_path.to_string(),
            rust_path: rust_path.to_string(),
        }
    }
}

/// Generate gRPC code from Protobuf using `tonic` library.
pub fn generate_grpc_code(
    proto_path: &str,
    file_paths: &[&str],
    options: CodegenOptions,
) -> std::io::Result<()> {
    set_protoc_env_if_unset();

    // TODO(#1093): Move all proto generation to a common crate.
    let proto_path = std::path::Path::new(proto_path);
    let file_paths: Vec<std::path::PathBuf> = file_paths
        .iter()
        .map(|file_path| proto_path.join(file_path))
        .collect();

    // Tell cargo to rerun this build script if the proto file has changed.
    // https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorerun-if-changedpath
    for file_path in file_paths.iter() {
        println!("cargo:rerun-if-changed={}", file_path.display());
    }

    // Generate the normal (non-Oak) server and client code for the gRPC service,
    // along with the Rust types corresponding to the message definitions.
    let mut config = tonic_build::configure()
        .build_client(options.build_client)
        .build_server(options.build_server);

    for extern_path in options.extern_paths {
        config = config.extern_path(extern_path.proto_path, extern_path.rust_path);
    }
    config.compile(&file_paths, &[proto_path.to_path_buf()])
}

fn set_protoc_env_if_unset() {
    if std::env::var("PROTOC").is_err() {
        // Use the system protoc if no override is set, so prost-build does not try to use the
        // bundled one that we remove as part of the vendoring process.
        std::env::set_var("PROTOC", "protoc");
    }
}
