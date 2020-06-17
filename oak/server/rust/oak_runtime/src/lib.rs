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

//! Oak Runtime implementation
//!
//! # Features
//!
//! The `oak_debug` feature enables various debugging features, including
//! data structure introspection functionality. This feature should only
//! be enabled in development, as it destroys the privacy guarantees of the
//! platform by providing easy channels for the exfiltration of private data.

use oak_abi::proto::oak::application::{ApplicationConfiguration, ConfigMap};

pub mod auth;
pub mod config;
pub mod proto;
pub mod time;

mod io;
mod message;
mod metrics;
mod node;
mod runtime;

use auth::oidc_utils::ClientInfo;
use message::NodeMessage;
use tonic::transport::{Certificate, Identity};

pub use config::configure_and_run;
pub use runtime::Runtime;

/// Configuration options that govern the behaviour of the Runtime and the Oak Application running
/// inside it.
#[derive(Default, Clone)]
pub struct RuntimeConfiguration {
    /// Port to run a metrics server on, if provided.
    pub metrics_port: Option<u16>,
    /// Port to run an introspection server on, if provided.
    pub introspect_port: Option<u16>,
    /// gRPC-specific options.
    pub grpc_config: GrpcConfiguration,
    /// Application configuration.
    pub app_config: ApplicationConfiguration,
    /// Start-of-day configuration to feed to the running Application.
    pub config_map: Option<ConfigMap>,
}

/// Configuration options related to gRPC pseudo-Nodes.
///
/// `Debug` is intentionally not implemented in order to avoid accidentally logging secrets.
#[derive(Default, Clone)]
pub struct GrpcConfiguration {
    /// TLS identity to use for all gRPC Server Nodes.
    pub grpc_server_tls_identity: Option<Identity>,

    /// OpenID Connect Authentication client information.
    pub oidc_client_info: Option<ClientInfo>,

    /// Root TLS certificate to use for all gRPC Client Nodes.
    // TODO(#999): Remove user-configurable root CA.
    pub grpc_client_root_tls_certificate: Option<Certificate>,
}
