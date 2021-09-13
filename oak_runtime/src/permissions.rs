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

use anyhow::{anyhow, Context};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, GrpcClientConfiguration, HttpClientConfiguration,
    NodeConfiguration,
};

/// Provides a declarative description of the features that are permitted
/// for an Oak application.
///
/// To run an Oak application, one must provide, as input to the `oak_loader`, a TOML
/// file of permissions, which is parsed into an instance of `PermissionsConfiguration`.
/// The permissions are applied dynamically at runtime, when creating the Nodes.
#[derive(Clone, Default, serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct PermissionsConfiguration {
    /// Whether to enable the use of GrpcServerNode.
    #[serde(default)]
    pub allow_grpc_server_nodes: bool,

    /// Whether to enable the use of HttpServerNode.
    #[serde(default)]
    pub allow_http_server_nodes: bool,

    /// Whether to enable the use of LogNode.
    #[serde(default)]
    pub allow_log_nodes: bool,

    /// Whether to enable creating an HTTP client for insecure HTTP connection. Such an
    /// HttpClientNode is configured with an empty authority, and does not use TLS connections.
    #[serde(default)]
    pub allow_insecure_http_egress: bool,

    /// List of the allowed authorities (of the form `[userinfo@]host[:port]`) that the application
    /// can connect to via a gRPC or an HTTP client. Only GrpcClientNodes or secure
    /// HttpClientNodes that are configured to connect to authorities in this list can be
    /// created. This is in addition to an insecure HttpClientNode that may be allowed via the
    /// `allow_insecure_http_egress` flag.
    #[serde(default)]
    pub allow_egress_https_authorities: Vec<String>,
}

impl PermissionsConfiguration {
    /// Check if this permissions configuration allows creating a node with the given node
    /// configuration. This check is disabled when `oak-unsafe` is enabled. In that case, this
    /// function returns `true` regardless of the node configuration.
    pub fn allowed_creation(&self, node_configuration: &NodeConfiguration) -> anyhow::Result<bool> {
        if cfg!(feature = "oak-unsafe") {
            Ok(true)
        } else {
            match &node_configuration.config_type {
                Some(ConfigType::LogConfig(_config)) => Ok(self.allow_log_nodes),
                Some(ConfigType::GrpcServerConfig(_config)) => Ok(self.allow_grpc_server_nodes),
                Some(ConfigType::GrpcClientConfig(config)) => self.allow_grpc_client(config),
                Some(ConfigType::HttpServerConfig(_config)) => Ok(self.allow_http_server_nodes),
                Some(ConfigType::HttpClientConfig(config)) => Ok(self.allow_http_client(config)),
                _ => Ok(true),
            }
        }
    }

    /// Checks if creating a GrpcClient node with the given configuration is permitted. Returns
    /// Ok(`true`) if the `authority` part of `config.uri` is in the list of allowed authorities.
    /// Returns an error if `config.uri` cannot be parsed into a URI object.
    pub fn allow_grpc_client(&self, config: &GrpcClientConfiguration) -> anyhow::Result<bool> {
        let uri = config
            .uri
            .parse::<http::Uri>()
            .context(format!("Error parsing URI {}", &config.uri))?;

        Ok(self.allow_egress_https_authorities.contains(
            &uri.authority()
                .ok_or_else(|| anyhow!("Empty authority"))?
                .to_string(),
        ))
    }

    /// Checks if creating an HttpClient node with the given configuration is permitted. If
    /// `config.authority` is empty, returns `true` if insecure HTTP connections are allowed. If
    /// `config.authority` is not empty, returns `true` if the authority is in the list of allowed
    /// authorities. Returns `false` otherwise.
    pub fn allow_http_client(&self, config: &HttpClientConfiguration) -> bool {
        config.authority.is_empty() && self.allow_insecure_http_egress
            || !config.authority.is_empty()
                && self
                    .allow_egress_https_authorities
                    .contains(&config.authority)
    }
}
