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

use std::net::SocketAddr;

use oak_session::{
    attestation::AttestationType,
    config::{SessionConfig, SessionConfigBuilder},
};
use serde::Deserialize;

use self::confidential_space::{ConfidentialSpaceGeneratorParams, ConfidentialSpaceVerifierParams};

#[derive(Deserialize)]
pub struct ClientConfig {
    pub listen_address: SocketAddr,
    pub server_proxy_address: SocketAddr,
    #[serde(default)]
    pub attestation_generators: Vec<GeneratorConfig>,
    #[serde(default)]
    pub attestation_verifiers: Vec<VerifierConfig>,
}

#[derive(Deserialize)]
pub struct ServerConfig {
    pub listen_address: SocketAddr,
    pub backend_address: SocketAddr,
    #[serde(default)]
    pub attestation_generators: Vec<GeneratorConfig>,
    #[serde(default)]
    pub attestation_verifiers: Vec<VerifierConfig>,
}

#[derive(Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum GeneratorConfig {
    ConfidentialSpace(ConfidentialSpaceGeneratorParams),
}

#[derive(Deserialize)]
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
