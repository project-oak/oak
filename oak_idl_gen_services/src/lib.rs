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

//! This crate allows compiling flatbuffer services to Rust in `build.rs` scripts.
//!
//! Also see the `oak_idl_gen_structs` crate.
//!
//! These crates are intentionally distinct so that `oak_idl_gen_services` can use
//! `oak_idl_gen_structs` in order to compile the flatbuffers reflection schema at compile time.

#![feature(path_file_prefix)]
#![feature(iter_intersperse)]

use anyhow::Context;
use convert_case::Casing;
use reflection_generated::reflection::{RPCCall, Service};
use std::process::exit;

mod reflection_generated {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/reflection_generated.rs"));
}

/// Compile services from the provided flatbuffer file using the `flatc` binary installed on the
/// system.
///
/// Services are generated targeting the invocation-based handler from the `oak_idl` crate (i.e.
/// not gRPC).
///
/// Each service method in the `rpc_service` definition must have a unique `method_id` numeric
/// attribute associated, which is used as part of the invocation serialization process. The
/// attribute must be declared upfront in the same file.
///
/// ```text
/// namespace Test;
///
/// attribute "method_id";
///
/// table Request {}
/// table Response {}
///
/// rpc_service Name {
///     Method(Request) : Response (method_id: 42);
/// }
/// ```
///
/// For a service called `TestName`, `compile_services` generates the following objects:
///
/// - a struct named `TestNameClient`, exposing a method for each method defined in the service.
///   This may be used to directly invoke the underlying handler in order to indirectly invoke
///   methods on the corresponding `Server` object on the other side of the handler.
/// - a struct named `TestNameServer`, which implements the `oak_idl::InvocationHandler` trait,
///   dispatching each request to the appropriate method on the underlying service implementation.
/// - a trait named `TestName`, with a method for each method defined in the macro, and an
///   additional default method named `serve` which returns an instance of `TestNameServer`; the
///   developer of a service would usually define a concrete struct and manually implement this
///   trait for it.
///
/// For an input flatbuffer file with name `test_file.fbs`, the generated Rust file will be located
/// at `${OUT_DIR}/test_file_services.rs`.
pub fn compile_services(filename: &str) {
    println!("cargo:rerun-if-changed={}", filename);
    // Run flatc to generate the reflected schema in flatbuffer binary format.
    let output = std::process::Command::new("flatc")
        .args([
            "--schema",
            "--binary",
            "-o",
            &std::env::var("OUT_DIR").unwrap(),
            filename,
        ])
        .output()
        .unwrap();
    if !output.status.success() {
        eprintln!("flatc exit code: {}", output.status);
        eprintln!(
            "flatc stdout: {}",
            std::str::from_utf8(&output.stdout).unwrap()
        );
        eprintln!(
            "flatc stderr: {}",
            std::str::from_utf8(&output.stderr).unwrap()
        );
        exit(1);
    }
    // We then read back the generated schema and parse it with the reflection flatbuffer schema.
    // See https://google.github.io/flatbuffers/intermediate_representation.html.
    let file_prefix = std::path::Path::new(filename)
        .file_prefix()
        .unwrap()
        .to_str()
        .unwrap();
    let schema_file = format!("{}/{}.bfbs", std::env::var("OUT_DIR").unwrap(), file_prefix);
    let schema_bytes = std::fs::read(&schema_file).unwrap();
    let generated_schema = generate_from_bytes(&schema_bytes).unwrap();
    let out_file = format!(
        "{}/{}_services.rs",
        std::env::var("OUT_DIR").unwrap(),
        file_prefix
    );
    std::fs::write(&out_file, generated_schema).unwrap();
}

/// Generate the Rust file from the input flatbuffer file.
///
/// In general, each flatbuffer file may have zero or more `rpc_service` instances defined.
///
/// We generate code by concatenating formatted strings because in the future we need to generate
/// code in other languages too, so we should not rely on anything that is specific to Rust here.
///
/// See
/// <https://github.com/google/flatbuffers/blob/9aa08a429e340bb8adf9b2e978ce2817cc8007c5/src/idl_gen_rust.cpp>
/// for how `flatc` generates Rust code for structs.
fn generate_from_bytes(schema_bytes: &[u8]) -> anyhow::Result<String> {
    let schema = reflection_generated::reflection::root_as_schema(schema_bytes)
        .context("could not parse schema")?;
    Ok(schema
        .services()
        .context("could not find any service definition")?
        .iter()
        .map(|s| generate_service(&s))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .intersperse("\n".to_string())
        .collect())
}

/// Generate the Rust objects from the input [`Service`] instance, corresponding to an `rpc_service`
/// entry.
fn generate_service(service: &Service) -> anyhow::Result<String> {
    let mut lines = Vec::new();
    lines.extend(vec![
        format!("// File automatically generated by `oak_idl_gen_services`, do not edit."),
        format!("// Original service name: {}", service.name()),
        format!(""),
        format!(
            "pub struct {}<T: oak_idl::Handler> {{",
            client_name(service)
        ),
        format!("    handler: T"),
        format!("}}"),
        format!(""),
        format!("impl <T: oak_idl::Handler>{}<T> {{", client_name(service)),
        format!("    pub fn new(handler: T) -> Self {{"),
        format!("        Self {{"),
        format!("            handler"),
        format!("        }}"),
        format!("    }}"),
    ]);
    lines.extend(
        service
            .calls()
            .context("could not find any call definitions")?
            .iter()
            .map(|c| generate_client_method(&c))
            .collect::<Result<Vec<_>, _>>()
            .context("could not generate client method")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![format!("}}"), format!("")]);
    lines.extend(vec![
        format!("pub struct {}<S> {{", server_name(service)),
        format!("    service: S"),
        format!("}}"),
        format!(""),
        format!(
            "impl <S: {}> oak_idl::Handler for {}<S> {{",
            service_name(service),
            server_name(service)
        ),
        format!("    fn invoke(&mut self, request: oak_idl::Request) -> Result<alloc::vec::Vec<u8>, oak_idl::Error> {{"),
        format!("        match request.method_id {{"),
    ]);
    lines.extend(
        service
            .calls()
            .context("could not find any call definitions")?
            .iter()
            .map(|c| generate_server_handler(&c))
            .collect::<Result<Vec<_>, _>>()
            .context("could not generate server handler")?
            .into_iter()
            .flatten(),
    );
    lines.extend(vec![
        format!("            _ => Err(oak_idl::Error::InvalidMethodId)"),
        format!("        }}"),
        format!("    }}"),
        format!("}}"),
        format!(""),
        format!("pub trait {}: Sized {{", service_name(service)),
    ]);
    lines.extend(
        service
            .calls()
            .context("could not find any call definitions")?
            .iter()
            .flat_map(|c| generate_service_method(&c)),
    );
    lines.extend(vec![
        format!("    fn serve(self) -> {}<Self> {{", server_name(service)),
        format!("        {} {{ service : self }}", server_name(service)),
        format!("    }}"),
        format!("}}"),
        format!(""),
    ]);
    Ok(lines.into_iter().intersperse("\n".to_string()).collect())
}

fn generate_client_method(rpc_call: &RPCCall) -> anyhow::Result<Vec<String>> {
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
            "    pub fn {}(&mut self, request_body: &[u8]) -> Result<oak_idl::utils::Message<{}>, oak_idl::Error> {{",
            method_name(rpc_call),
            response_type(rpc_call)
        ),
        format!(
            "        flatbuffers::root::<{}>(request_body).map_err(|_err| oak_idl::Error::InvalidRequest)?;",
            request_type(rpc_call)
        ),
        format!("        let request = oak_idl::Request {{"),
        format!("            method_id: {},", method_id(rpc_call)?),
        format!("            body: request_body,"),
        format!("        }};"),
        format!("        let response_body = self.handler.invoke(request)?;"),
        format!("        oak_idl::utils::Message::from_vec(response_body).map_err(|_err| oak_idl::Error::InvalidResponse)"),
        format!("    }}"),
    ])
}

fn generate_server_handler(rpc_call: &RPCCall) -> anyhow::Result<Vec<String>> {
    // This handler appears inside a `match` block in the server implementation. Its purpose is to
    // parse the incoming request buffer as an object of the correct type, and dispatch a reference
    // to that object to the underlying service implementation, provided by the developer, which
    // deals with type safe generated objects instead of raw buffers.
    Ok(vec![
        format!("            {} => {{", method_id(rpc_call)?),
        format!(
            "                let request = flatbuffers::root::<{}>(request.body).map_err(|_err| oak_idl::Error::InvalidRequest)?;",
            request_type(rpc_call),
        ),
        format!(
            "                let response = self.service.{}(&request);",
            method_name(rpc_call),
        ),
        format!("                let response_body = response.buf().to_vec();"),
        format!("                Ok(response_body)"),
        format!("            }}",),
    ])
}

fn generate_service_method(rpc_call: &RPCCall) -> Vec<String> {
    // Note the asymmetry between input and output types; the input type is a reference to an
    // object, whose buffer is owned by the caller, while the returned object is created by the
    // implementation of this method, therefore needs to be wrapped in `oak_idl::Message` in order
    // to transfer its ownership to the caller.
    vec![format!(
        "    fn {}(&self, request: &{}) -> oak_idl::utils::Message<{}>;",
        method_name(rpc_call),
        request_type(rpc_call),
        response_type(rpc_call)
    )]
}

/// Returns the `method_id` attribute on the [`RPCCall`]. This is used to identify methods in a
/// backwards compabile way and without relying on their name or their ordering.
///
/// The `method_id` attribute must be declared upfront in each input flatbuffer file.
fn method_id(rpc_call: &RPCCall) -> anyhow::Result<u32> {
    rpc_call
        .attributes()
        .context("could not find any attributes on method")?
        .iter()
        .find(|kv| kv.key() == "method_id")
        .ok_or_else(|| {
            anyhow::anyhow!(
                "method_id attribute not found on method {}",
                rpc_call.name()
            )
        })?
        .value()
        .context("could not find attribute value")?
        .parse::<u32>()
        .map_err(|err| {
            anyhow::anyhow!(
                "could not parse method_id attribute on method {}: {}",
                rpc_call.name(),
                err
            )
        })
}

/// The type name of the generated Rust client struct.
fn client_name(service: &Service) -> String {
    format!("{}Client", unqualified_name(service.name()))
}

/// The type name of the generated Rust server struct.
fn server_name(service: &Service) -> String {
    format!("{}Server", unqualified_name(service.name()))
}

/// The type name of the generated Rust service struct.
fn service_name(service: &Service) -> String {
    unqualified_name(service.name())
}

/// The method name of the generated Rust client method.
fn method_name(rpc_call: &RPCCall) -> String {
    rpc_call.name().to_case(convert_case::Case::Snake)
}

/// The type name of the generated Rust request struct.
fn request_type(rpc_call: &RPCCall) -> String {
    qualified_name(rpc_call.request().name())
}

/// The type name of the generated Rust response struct.
fn response_type(rpc_call: &RPCCall) -> String {
    qualified_name(rpc_call.response().name())
}

/// Returns the last part of the name, splitting on `.`.
fn unqualified_name(qualified_name: &str) -> String {
    qualified_name
        .split('.')
        .last()
        // If split returned an empty iterator, then the input name did not contain any dots, so we
        // can return it as-is.
        .unwrap_or(qualified_name)
        .to_string()
}

#[test]
fn test_unqualified_name() {
    assert_eq!("Message", unqualified_name("foo.bar.Message"));
    assert_eq!("Message", unqualified_name("Message"));
}

/// Returns a fully qualified Rust type corresponding to the provided name.
fn qualified_name(qualified_name: &str) -> String {
    let mut parts: Vec<&str> = qualified_name.split('.').collect();
    let last = parts.pop().unwrap();
    parts
        .into_iter()
        .map(|p| p.to_case(convert_case::Case::Snake))
        .chain([last.to_string()])
        .intersperse("::".to_string())
        .collect()
}

#[test]
fn test_qualified_name() {
    assert_eq!("foo::bar::Message", qualified_name("foo.bar.Message"));
    assert_eq!("Message", qualified_name("Message"));
}
