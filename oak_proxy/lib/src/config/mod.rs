//
// Copyright 2025 The Project Oak Authors
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

pub mod confidential_space;

use std::{net::SocketAddr, time::Duration};

use oak_session::{
    attestation::AttestationType,
    config::{SessionConfig, SessionConfigBuilder},
};
use serde::{Deserialize, Serialize};
use url::Url;

use self::confidential_space::{ConfidentialSpaceGeneratorParams, ConfidentialSpaceVerifierParams};

fn default_keep_alive_interval() -> Duration {
    Duration::from_secs(10)
}

pub fn load_toml<T>(path: &str) -> anyhow::Result<T>
where
    T: for<'de> Deserialize<'de>,
{
    let config_str = std::fs::read_to_string(path)?;
    let config: T = toml::from_str(&config_str)?;

    Ok(config)
}

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct ClientConfig {
    #[serde(default)]
    pub listen_address: Option<SocketAddr>,
    #[serde(default)]
    pub server_proxy_url: Option<Url>,
    #[serde(with = "humantime_serde", default = "default_keep_alive_interval")]
    pub keep_alive_interval: Duration,
    #[serde(default)]
    pub attestation_generators: Vec<GeneratorConfig>,
    #[serde(default)]
    pub attestation_verifiers: Vec<VerifierConfig>,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct ServerConfig {
    #[serde(default)]
    pub listen_address: Option<SocketAddr>,
    #[serde(default)]
    pub backend_address: Option<SocketAddr>,
    #[serde(with = "humantime_serde", default = "default_keep_alive_interval")]
    pub keep_alive_interval: Duration,
    #[serde(default)]
    pub attestation_generators: Vec<GeneratorConfig>,
    #[serde(default)]
    pub attestation_verifiers: Vec<VerifierConfig>,
    #[serde(default)]
    pub backend_command: Option<CommandConfig>,
}

#[derive(Deserialize, Serialize, Debug, Clone, Copy, Default)]
#[serde(rename_all = "snake_case")]
pub enum RestartPolicy {
    /// The backend process crashing causes the proxy to terminate.
    #[default]
    Terminate,
    /// The backend process is restarted by the proxy after a crash.
    Always,
    /// The backend process is not restarted by the proxy after a crash,
    /// but the proxy does not terminate.
    Never,
}

#[derive(Deserialize, Serialize, Debug, Clone, Default)]
pub struct CommandConfig {
    pub cmd: String,
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default)]
    pub restart_policy: RestartPolicy,
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum GeneratorConfig {
    ConfidentialSpace(ConfidentialSpaceGeneratorParams),
}

#[derive(Deserialize, Serialize, Debug, Clone)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum VerifierConfig {
    ConfidentialSpace(ConfidentialSpaceVerifierParams),
}

impl GeneratorConfig {
    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        match self {
            GeneratorConfig::ConfidentialSpace(params) => params.apply(builder),
        }
    }
}

impl VerifierConfig {
    pub fn apply(&self, builder: SessionConfigBuilder) -> anyhow::Result<SessionConfigBuilder> {
        match self {
            VerifierConfig::ConfidentialSpace(params) => params.apply(builder),
        }
    }
}

pub fn build_session_config(
    attestation_generators: &Vec<GeneratorConfig>,
    attestation_verifiers: &Vec<VerifierConfig>,
) -> anyhow::Result<SessionConfig> {
    let attestation_type =
        match (attestation_generators.is_empty(), attestation_verifiers.is_empty()) {
            (true, true) => AttestationType::Unattested,
            (true, false) => AttestationType::PeerUnidirectional,
            (false, true) => AttestationType::SelfUnidirectional,
            (false, false) => AttestationType::Bidirectional,
        };

    let mut builder =
        SessionConfig::builder(attestation_type, oak_session::handshake::HandshakeType::NoiseNN);

    for generator in attestation_generators {
        builder = generator.apply(builder)?;
    }

    for verifier in attestation_verifiers {
        builder = verifier.apply(builder)?;
    }

    Ok(builder.build())
}
