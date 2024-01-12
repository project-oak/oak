//
// Copyright 2023 The Project Oak Authors
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

pub mod proto {
    pub mod oak {
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::attestation;
        pub mod session {
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                #![allow(clippy::large_enum_variant)]
                tonic::include_proto!("oak.session.v1");
            }
        }
    }
}

pub mod transport;
pub mod verifier;

use std::vec::Vec;

use anyhow::{anyhow, Context};
use oak_crypto::encryptor::ClientEncryptor;

use crate::transport::{EvidenceProvider, Transport};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient<T: Transport> {
    transport: T,
    server_encryption_public_key: Vec<u8>,
}

impl<T: Transport + EvidenceProvider> OakClient<T> {
    pub async fn create(mut transport: T) -> anyhow::Result<Self> {
        // TODO(#3641): Implement client-side attestation verification.
        let evidence = transport
            .get_evidence()
            .await
            .context("couldn't get attestation evidence")?;
        Ok(Self {
            transport,
            server_encryption_public_key: evidence.encryption_public_key.to_vec(),
        })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Encrypt request.
        let mut client_encryptor = ClientEncryptor::create(&self.server_encryption_public_key)
            .context("couldn't create encryptor")?;
        let encrypted_request = client_encryptor
            .encrypt(request_body, EMPTY_ASSOCIATED_DATA)
            .context("couldn't encrypt request")?;

        // Send request.
        let encrypted_response = self
            .transport
            .invoke(&encrypted_request)
            .await
            .map_err(|error| anyhow!("couldn't send request: {:?}", error))?;

        // Decrypt response.
        // Currently we ignore the associated data.
        let (response, _) = client_encryptor
            .decrypt(&encrypted_response)
            .context("client couldn't decrypt response")?;

        Ok(response)
    }
}
