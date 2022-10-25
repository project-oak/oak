//
// Copyright 2022 The Project Oak Authors
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

#![feature(iter_intersperse)]

//! This crate allows compiling protobuf services to Rust in `build.rs` scripts.

use anyhow::Context;
use prost_build::{Method, Service};

/// Compile Rust server code from the services in the provided protobuf file.
///
/// Each method in a service definition must have exactly one comment line of the form `//
/// method_id: 42`, which is used to generate a stable identifier for that method, which is part of
/// the serialization protocol used for invocation.
///
/// For a service called `TestName`, `compile` generates the following objects:
///
/// - a struct named `TestNameServer`, which implements the `oak_idl::InvocationHandler` trait,
///   dispatching each request to the appropriate method on the underlying service implementation.
/// - a trait named `TestName`, with a method for each method defined in the protobuf service, and
///   an additional default method named `serve` which returns an instance of `TestNameServer`; the
///   developer of a service would usually define a concrete struct and manually implement this
///   trait for it,
/// - a struct named `TestNameClient`, exposing a method for each method defined in the protobuf
///   service. This may be used to directly invoke the underlying handler in order to indirectly
///   invoke methods on the corresponding `Server` object on the other side of the handler.
/// - a struct named `TestNameAsyncClient`, similar to `TestNameClient` but with async support.
pub fn compile(filename: &str) {
    println!("cargo:rerun-if-changed={}", filename);
    let mut config = prost_build::Config::new();
    config.service_generator(Box::new(ServiceGenerator {}));
    config
        .compile_protos(&[filename], &["."])
        .expect("could not compile protobuffer schema");
}

struct ServiceGenerator {}

impl prost_build::ServiceGenerator for ServiceGenerator {
    fn generate(&mut self, service: Service, buf: &mut String) {
        *buf += "\n";
        *buf += &generate_service(&service).expect("could not generate services");
        *buf += "\n";
        *buf += &generate_service_client(&service, false).expect("could not generate clients");
        *buf += "\n";
        *buf += &generate_service_client(&service, true).expect("could not generate async clients");
    }
}

/// Generate the Rust objects from the input [`Service`] instance, corresponding to a `service`
/// entry.
fn generate_service(service: &Service) -> anyhow::Result<String> {
    let mut lines = Vec::new();
    lines.extend(vec![
        format!("pub struct {}<S> {{", server_name(service)),
        format!("    service: S"),
        format!("}}"),
        format!(""),
        format!(
            "impl <S: {}> ::oak_idl::Handler for {}<S> {{",
            service_name(service),
            server_name(service)
        ),
        format!("    fn invoke(&mut self, request: ::oak_idl::Request) -> Result<::prost::alloc::vec::Vec<u8>, ::oak_idl::Status> {{"),
        format!("        match request.method_id {{"),
    ]);
    lines.extend(
        service
            .methods
            .iter()
            .map(generate_server_handler)
            .collect::<Result<Vec<_>, _>>()
            .context("could not generate server handler")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![
        format!(
            "            _ => Err(::oak_idl::Status::new(::oak_idl::StatusCode::Unimplemented))"
        ),
        format!("        }}"),
        format!("    }}"),
        format!("}}"),
        format!(""),
        format!("pub trait {}: Sized {{", service_name(service)),
    ]);
    lines.extend(service.methods.iter().flat_map(generate_service_method));
    lines.extend(vec![
        format!("    fn serve(self) -> {}<Self> {{", server_name(service)),
        format!("        {} {{ service : self }}", server_name(service)),
        format!("    }}"),
        format!("}}"),
        format!(""),
    ]);
    Ok(lines.into_iter().intersperse("\n".to_string()).collect())
}

/// Generate the service client Rust objects from the input [`Service`] instance, corresponding to
/// an `rpc` entry.
fn generate_service_client(service: &Service, asynchronous: bool) -> anyhow::Result<String> {
    let client_name = client_name(service, asynchronous);
    let handler_trait = if asynchronous {
        "::oak_idl::AsyncHandler"
    } else {
        "::oak_idl::Handler"
    };
    let mut lines = Vec::new();
    lines.extend(vec![
        format!("pub struct {}<T: {}> {{", client_name, handler_trait),
        format!("    handler: T"),
        format!("}}"),
        format!(""),
        format!("impl <T: {}>{}<T> {{", handler_trait, client_name),
        format!("    pub fn new(handler: T) -> Self {{"),
        format!("        Self {{"),
        format!("            handler"),
        format!("        }}"),
        format!("    }}"),
    ]);
    lines.extend(
        service
            .methods
            .iter()
            .map(|c| generate_client_method(c, asynchronous))
            .collect::<Result<Vec<_>, _>>()
            .context("could not generate client method")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![format!("}}"), format!("")]);
    Ok(lines.into_iter().intersperse("\n".to_string()).collect())
}

fn generate_client_method(method: &Method, asynchronous: bool) -> anyhow::Result<Vec<String>> {
    // For each method on the schema, generate a client method with the same name, accepting a
    // buffer containing the serialized request as input. Unfortunately it does not seem easy to
    // make this more type safe than this; ideally it would take a reference to a message of the
    // correct type.
    //
    // The return value is wrapped in an `oak_idl::Message` since it is owned by the implementation
    // of this method and needs to be passed to the caller; building a buffer within the generated
    // method and returning an object that points to it would not work because of the mismatch in
    // lifetimes. In principle it should be possible though if the caller passes in the buffer to
    // fill in, which would remain owned by the caller, but that seems more complicated and for not
    // much benefit.
    Ok(vec![
            format!(
                "    pub {}fn {}(&mut self, request: &{}) -> Result<{}, ::oak_idl::Status> {{",
                if asynchronous {"async "} else {""},
                method_name(method),
                request_type(method),
                response_type(method)
            ),
            format!("        use ::prost::Message;"),
            format!("        let request_body = request.encode_to_vec();"),
            format!("        let request = ::oak_idl::Request {{"),
            format!("            method_id: {},", method_id(method)?),
            format!("            body: request_body,"),
            format!("        }};"),
            format!("        let response_body = self.handler.invoke(request){}?;", if asynchronous {".await"} else {""}),
            format!("        {}::decode(response_body.as_ref()).map_err(|err| ::oak_idl::Status::new_with_message(::oak_idl::StatusCode::Internal, format!(\"Client failed to deserialize the response: {{:?}}\", err)))", response_type(method)),
            format!("    }}"),
        ])
}

fn generate_server_handler(method: &Method) -> anyhow::Result<Vec<String>> {
    // This handler appears inside a `match` block in the server implementation. Its purpose is to
    // parse the incoming request buffer as an object of the correct type, and dispatch a reference
    // to that object to the underlying service implementation, provided by the developer, which
    // deals with type safe generated objects instead of raw buffers.
    Ok(vec![
        format!("            {} => {{", method_id(method)?),
        format!("                use ::prost::Message;"),
        format!(
            "                let request = {}::decode(request.body.as_ref()).map_err(|err| ::oak_idl::Status::new_with_message(::oak_idl::StatusCode::Internal, format!(\"Service failed to deserialize the request: {{:?}}\", err)))?;",
            request_type(method),
        ),
        format!(
            "                let response = self.service.{}(&request)?;",
            method_name(method),
        ),
        format!("                let response_body = response.encode_to_vec();"),
        format!("                Ok(response_body)"),
        format!("            }}",),
    ])
}

fn generate_service_method(method: &Method) -> Vec<String> {
    vec![format!(
        "    fn {}(&mut self, request: &{}) -> Result<{}, ::oak_idl::Status>;",
        method_name(method),
        request_type(method),
        response_type(method)
    )]
}

/// Returns the value of the `method_id` commend on the method.
fn method_id(method: &Method) -> anyhow::Result<u32> {
    let method_ids = method
        .comments
        .leading
        .iter()
        .filter_map(|line| line.strip_prefix(" method_id: "))
        .collect::<Vec<_>>();
    if method_ids.is_empty() {
        anyhow::bail!("no method_id comment on method {}", method.proto_name,)
    } else if method_ids.len() > 1 {
        anyhow::bail!(
            "multiple method_id comments on method {}",
            method.proto_name
        )
    } else {
        Ok(method_ids[0].parse()?)
    }
}

/// The type name of the generated Rust client struct.
fn client_name(service: &Service, asynchronous: bool) -> String {
    format!(
        "{}{}",
        service.name,
        if asynchronous {
            "AsyncClient"
        } else {
            "Client"
        }
    )
}

/// The type name of the generated Rust server struct.
fn server_name(service: &Service) -> String {
    format!("{}Server", service.name)
}

/// The type name of the generated Rust service struct.
fn service_name(service: &Service) -> String {
    service.name.to_string()
}

/// The method name of the generated Rust client method.
fn method_name(method: &Method) -> String {
    method.name.to_string()
}

/// The type name of the generated Rust request struct.
fn request_type(method: &Method) -> String {
    method.input_type.to_string()
}

/// The type name of the generated Rust response struct.
fn response_type(method: &Method) -> String {
    method.output_type.to_string()
}
