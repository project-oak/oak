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
use std::path::PathBuf;

use anyhow::Context;
mod prost;

pub use prost::compile;

#[derive(Default, Clone)]
pub struct ExternPath {
    proto_path: String,
    rust_path: String,
}

impl ExternPath {
    pub fn new(proto_path: &str, rust_path: &str) -> Self {
        ExternPath { proto_path: proto_path.to_string(), rust_path: rust_path.to_string() }
    }
}
#[derive(Copy, Clone, Debug, Default)]
pub enum ReceiverType {
    /// &mut self
    #[default]
    RefMutSelf,

    /// &self
    RefSelf,
}

impl ReceiverType {
    fn value(&self) -> &'static str {
        match self {
            ReceiverType::RefMutSelf => "&mut self",
            ReceiverType::RefSelf => "&self",
        }
    }
}

#[derive(Default, Clone)]
pub struct CompileOptions {
    /// Specifies the receiver type in generated server code.
    pub receiver_type: ReceiverType,

    /// List of `bytes` fields that will use `bytes::Bytes` instead of `Vec<u8>`
    pub bytes: Vec<String>,

    /// Specifies externally provided Protobuf packages or types.
    pub extern_paths: Vec<ExternPath>,

    /// Configures the code generator to include type names.
    ///
    /// Message types will implement `Name` trait, which provides type and
    /// package name. This is needed for encoding messages as `Any` type.
    ///
    /// See https://docs.rs/prost-build/0.12.4/prost_build/struct.Config.html#method.enable_type_names
    pub enable_type_names: bool,

    // Configures the directory into which generated files will be written.
    ///
    /// Defaults to the OUT_DIR env variable, if unset.
    ///
    /// See https://docs.rs/prost-build/latest/prost_build/struct.Config.html#method.out_dir.
    pub out_dir: Option<PathBuf>,

    // Configures the path to the protoc executable.
    ///
    /// Defaults to the PROTOC env variable, if unset.
    ///
    /// See https://docs.rs/prost-build/latest/prost_build/struct.Config.html#method.protoc_executable.
    pub protoc_executable: Option<PathBuf>,
}
/// A service definition to generate micro_rpc code for.
#[derive(Debug)]
pub struct Service {
    pub name: String,
    pub methods: Vec<Method>,
}

#[derive(Debug)]
pub struct Method {
    pub name: String,
    pub id: u32,
    pub input_type: String,
    pub output_type: String,
}

pub fn generate_file(service: &Service, receiver_type: ReceiverType, buf: &mut String) {
    *buf += "\n";
    *buf += &generate_service(service, receiver_type).expect("couldn't generate services");
    *buf += "\n";
    *buf += &generate_service_client(service, false).expect("couldn't generate clients");
    *buf += "\n";
    *buf += &generate_service_client(service, true).expect("couldn't generate async clients");
}

/// Generate the Rust objects from the input [`Service`] instance, corresponding
/// to a `service` entry.
fn generate_service(service: &Service, receiver_type: ReceiverType) -> anyhow::Result<String> {
    let service_name = &service.name;
    let server_name = server_name(service_name);
    let mut lines = Vec::new();
    lines.extend(vec![
        format!("#[derive(Clone)]"),
        format!("pub struct {server_name}<S> {{"),
        format!("    service: S"),
        format!("}}"),
        format!(""),
        format!("impl <S: {service_name}> ::micro_rpc::Transport for {server_name}<S> {{"),
        format!("    fn invoke(&mut self, request_bytes: &[u8]) -> Result<::prost::alloc::vec::Vec<u8>, !> {{"),
        format!("        let response: ::micro_rpc::ResponseWrapper = self"),
        format!("            .invoke_inner(request_bytes)"),
        format!("            .into();"),
        format!("        let response_bytes = response.encode_to_vec();"),
        format!("        Ok(response_bytes)"),
        format!("    }}"),
        format!("}}"),
        format!(""),
        format!("impl <S: {service_name}> {server_name}<S> {{"),
        format!("    pub fn new(service: S) -> Self {{"),
        format!("        Self {{ service }}"),
        format!("    }}"),
        // invoke_inner returns either a successful response body, or an error represented as Status.
        format!("    fn invoke_inner(&mut self, request_bytes: &[u8]) -> Result<::prost::alloc::vec::Vec<u8>, ::micro_rpc::Status> {{"),
        format!("        let request = ::micro_rpc::RequestWrapper::decode(request_bytes).map_err(|err| {{"),
        format!("            ::micro_rpc::Status::new_with_message("),
        format!("                ::micro_rpc::StatusCode::Internal,"),
        format!("                ::micro_rpc::format!(\"Client failed to deserialize the response: {{:?}}\", err),"),
        format!("            )"),
        format!("        }})?;"),
        format!("        match request.method_id {{"),
    ]);
    lines.extend(
        service
            .methods
            .iter()
            .map(generate_server_handler)
            .collect::<Result<Vec<_>, _>>()
            .context("couldn't generate server handler")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![
        format!("            _ => Err(::micro_rpc::Status::new("),
        format!("                ::micro_rpc::StatusCode::Unimplemented,"),
        format!("            ))"),
        format!("        }}"),
        format!("    }}"),
        format!("}}"),
        format!(""),
        format!("pub trait {service_name}: Sized {{"),
    ]);
    lines.extend(
        service.methods.iter().flat_map(|method| generate_service_method(method, receiver_type)),
    );
    lines.extend(vec![format!("}}"), format!("")]);
    Ok(lines.into_iter().intersperse("\n".to_string()).collect())
}

/// Generate the service client Rust objects from the input [`Service`]
/// instance, corresponding to an `rpc` entry.
fn generate_service_client(service: &Service, asynchronous: bool) -> anyhow::Result<String> {
    let client_name = client_name(service, asynchronous);
    let transport_trait =
        if asynchronous { "::micro_rpc::AsyncTransport" } else { "::micro_rpc::Transport" };
    let mut lines = Vec::new();
    lines.extend(vec![
        format!("pub struct {client_name}<T: {transport_trait}> {{",),
        format!("    transport: T"),
        format!("}}"),
        format!(""),
        format!("impl <T: {transport_trait}> {client_name}<T> {{"),
        format!("    pub fn new(transport: T) -> Self {{"),
        format!("        Self {{"),
        format!("            transport"),
        format!("        }}"),
        format!("    }}"),
    ]);
    lines.extend(
        service
            .methods
            .iter()
            .map(|c| generate_client_method(c, asynchronous))
            .collect::<Result<Vec<_>, _>>()
            .context("couldn't generate client method")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![format!("}}"), format!("")]);
    Ok(lines.into_iter().intersperse("\n".to_string()).collect())
}

fn generate_client_method(method: &Method, asynchronous: bool) -> anyhow::Result<Vec<String>> {
    let method_id = method.id;
    let request_type = &method.input_type;
    let response_type = &method.output_type;
    let method_name = &method.name;
    let fn_modifier = if asynchronous { "async " } else { "" };
    Ok(vec![
        format!(
            "    pub {fn_modifier}fn {method_name}(&mut self, request: &{request_type}) -> Result<Result<{response_type}, ::micro_rpc::Status>, T::Error> {{"
        ),
        if asynchronous {
            format!(
                "        ::micro_rpc::async_client_invoke(&mut self.transport, {method_id}, request).await"
            )
        } else {
            format!("        ::micro_rpc::client_invoke(&mut self.transport, {method_id}, request)")
        },
        format!("    }}"),
    ])
}

fn generate_server_handler(method: &Method) -> anyhow::Result<Vec<String>> {
    // This handler appears inside a `match` block in the server implementation. Its
    // purpose is to parse the incoming request buffer as an object of the
    // correct type, and dispatch a reference to that parsed object to the
    // underlying service implementation, provided by the developer, which deals
    // with type safe generated objects instead of raw byte buffers.
    let method_id = method.id;
    let request_type = &method.input_type;
    let method_name = &method.name;
    Ok(vec![
        format!("            {method_id} => {{"),
        // We need the angle brackets around the type in order to make sure it works with Rust well
        // known types, e.g. when `google.protobuf.Empty` is replaced by `()`.
        format!("                let request = <{request_type}>::decode(request.body.as_ref()).map_err(|err| {{"),
        format!("                    ::micro_rpc::Status::new_with_message("),
        format!("                        ::micro_rpc::StatusCode::Internal,"),
        format!(
            "                        ::micro_rpc::format!(\"Service failed to deserialize the request: {{:?}}\", err)"
        ),
        format!("                    )"),
        format!("                }})?;"),
        format!("                let response = self.service.{method_name}(request)?;"),
        format!("                let response_body = response.encode_to_vec();"),
        format!("                Ok(response_body)"),
        format!("            }}",),
    ])
}

fn generate_service_method(method: &Method, receiver_type: ReceiverType) -> Vec<String> {
    let method_name = &method.name;
    let request_type = &method.input_type;
    let response_type = &method.output_type;
    let self_type = receiver_type.value();
    vec![format!(
        "    fn {method_name}({self_type}, request: {request_type}) -> Result<{response_type}, ::micro_rpc::Status>;"
    )]
}

/// The type name of the generated Rust server struct.
fn server_name(service_name: &str) -> String {
    format!("{}Server", service_name)
}

/// The type name of the generated Rust client struct.
fn client_name(service: &Service, asynchronous: bool) -> String {
    format!("{}{}", service.name, if asynchronous { "AsyncClient" } else { "Client" })
}
