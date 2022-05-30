//
// Copyright 2021 The Project Oak Authors
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

use oak_functions_abi::proto::ConfigurationInfo;
use oak_remote_attestation::{handshaker::ServerIdentityVerifier, message::ServerIdentity};
use prost::Message;

pub type ConfigurationVerifier = fn(ConfigurationInfo) -> anyhow::Result<()>;

/// Creates a [`ServerIdentityVerifier`] from the given `ConfigurationVerifier`.
///
/// The `ServerIdentityVerifier` parses the byte array in `server_identity.additional_info` into a
/// `ConfigurationInfo` object. If the conversion is successful, `config_verifier` is invoked to
/// verify the `ConfigurationInfo` object. Otherwise, an error is returned. An error is as well
/// returned if the call to `config_verifier` returns an error.
pub fn into_server_identity_verifier(
    config_verifier: ConfigurationVerifier,
) -> ServerIdentityVerifier {
    let server_verifier = move |server_identity: &ServerIdentity| -> anyhow::Result<()> {
        let config =
            ConfigurationInfo::decode(server_identity.additional_info.as_ref().as_slice())?;
        // TODO(#2347): Check that ConfigurationInfo does not have additional/unknown fields.
        config_verifier(config)?;
        // TODO(#2316): Verify proof of inclusion in Rekor.
        Ok(())
    };

    Box::new(server_verifier)
}
