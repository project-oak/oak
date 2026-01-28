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

//! This crate allows compiling protobuf services to Rust in `build.rs` scripts.

use std::path::Path;

/// Compile Rust server code from the services in the provided protobuf file.
///
/// Each method in a service definition must have exactly one comment line of
/// the form `// method_id: 42`, which is used to generate a stable identifier
/// for that method, which is part of the serialization protocol used for
/// invocation.
///
/// For a service called `TestName`, `compile` generates the following objects:
///
/// - a struct named `TestNameServer`, which implements the
///   `micro_rpc::InvocationHandler` trait, dispatching each request to the
///   appropriate method on the underlying service implementation.
/// - a trait named `TestName`, with a method for each method defined in the
///   protobuf service, and an additional default method named `serve` which
///   returns an instance of `TestNameServer`; the developer of a service would
///   usually define a concrete struct and manually implement this trait for it,
/// - a struct named `TestNameClient`, exposing a method for each method defined
///   in the protobuf service. This may be used to directly invoke the
///   underlying handler in order to indirectly invoke methods on the
///   corresponding `Server` object on the other side of the handler.
/// - a struct named `TestNameAsyncClient`, similar to `TestNameClient` but with
///   async support.
pub fn compile(
    protos: &[impl AsRef<Path>],
    includes: &[impl AsRef<Path>],
    options: crate::CompileOptions,
) {
    let mut config = prost_build::Config::new();
    config.service_generator(Box::new(ServiceGenerator { options: options.clone() }));
    for extern_path in options.extern_paths {
        config.extern_path(extern_path.proto_path, extern_path.rust_path);
    }
    if options.enable_type_names {
        config.enable_type_names();
    }
    if let Some(out_dir) = options.out_dir {
        config.out_dir(out_dir);
    }
    if let Some(protoc_executable) = options.protoc_executable {
        config.protoc_executable(protoc_executable);
    }
    config
        // Use BTreeMap to allow using this function in no-std crates.
        .btree_map(["."])
        .bytes(options.bytes)
        .compile_protos(protos, includes)
        .expect("couldn't compile protobuffer schema");
}

struct ServiceGenerator {
    options: crate::CompileOptions,
}

impl prost_build::ServiceGenerator for ServiceGenerator {
    fn generate(&mut self, service: prost_build::Service, buf: &mut String) {
        let service: crate::Service = (&service).into();
        crate::generate_file(&service, self.options.receiver_type, buf);
    }
}

impl From<&prost_build::Service> for crate::Service {
    fn from(src: &prost_build::Service) -> crate::Service {
        crate::Service {
            name: src.name.to_string(),
            methods: src.methods.iter().map(|m| m.into()).collect(),
        }
    }
}

impl From<&prost_build::Method> for crate::Method {
    fn from(src: &prost_build::Method) -> crate::Method {
        crate::Method {
            name: src.name.to_string(),
            id: method_id(src).expect("missing method id"),
            input_type: src.input_type.to_string(),
            output_type: src.output_type.to_string(),
        }
    }
}

/// Returns the value of the `method_id` comment on the method.
fn method_id(method: &prost_build::Method) -> anyhow::Result<u32> {
    let method_ids = method
        .comments
        .leading
        .iter()
        .filter_map(|line| line.strip_prefix("method_id: "))
        .collect::<Vec<_>>();
    if method_ids.is_empty() {
        anyhow::bail!("no method_id comment on method {}", method.proto_name)
    } else if method_ids.len() > 1 {
        anyhow::bail!("multiple method_id comments on method {}", method.proto_name)
    } else {
        Ok(method_ids[0].parse()?)
    }
}
