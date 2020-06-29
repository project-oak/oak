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

/// Provides a declarative description of the features that are permitted
/// for an Oak application.
///
/// To run an Oak application, one must provide, as input to the `oak_loader`, a TOML
/// file of permissions, which is parsed into an instance of `PermissionsConfiguration`.
/// The permissions are applied dynamically at runtime, when creating the Nodes.
#[allow(dead_code)]
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct PermissionsConfiguration {
    /// Whether to enable the use of GrpcServerNode.
    #[serde(default)]
    allow_grpc_server_nodes: bool,

    /// Whether to enable the use of HttpServerNode.
    #[serde(default)]
    allow_http_server_nodes: bool,

    /// Whether to enable the use of LogNode.
    #[serde(default)]
    allow_log_nodes: bool,

    /// Whether to allow introspection. If true, the introspection auxiliary service will be
    /// started.
    #[serde(default)]
    allow_introspection: bool,

    /// List of the allowed URIs that the application can connect to. Only GrpcClientNodes
    /// that are configured to connect to URIs in this list can be created.
    #[serde(default)]
    allow_grpc_egress_addresses: Vec<String>,
}
