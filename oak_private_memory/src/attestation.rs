// Copyright 2026 The Project Oak Authors
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

//! Production attestation configuration.
//!
//! Uses `Unattested` attestation type until real attestation evidence is
//! available. For dummy/test attestation implementations, see the
//! `attestation_testing` crate (testonly).

use oak_session::{attestation::AttestationType, config::SessionConfig, handshake::HandshakeType};

/// Creates the default server-side `SessionConfig` using no attestation.
///
/// This will be upgraded to use real attestation once evidence is available.
pub fn default_server_session_config() -> SessionConfig {
    SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build()
}
