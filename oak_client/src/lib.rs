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
    #![allow(clippy::return_self_not_must_use)]
    tonic::include_proto!("oak.session.noninteractive.v1");
}

pub mod transport;
pub mod verifier;

use crate::{
    transport::AsyncTransport,
    verifier::{EvidenceProvider, ReferenceValue, Verifier},
};
use anyhow::Context;
use std::{vec, vec::Vec};

/// Client for connecting to Oak.
/// Represents a Relying Party from the RATS Architecture:
/// <https://www.rfc-editor.org/rfc/rfc9334.html#name-relying-party>
pub struct OakClient {
    transport: Box<dyn AsyncTransport>,
    encryptor: Encryptor,
}

impl OakClient {
    pub fn create(
        transport: Box<dyn AsyncTransport>,
        mut evidence_provider: Box<dyn EvidenceProvider>,
        reference_value: ReferenceValue,
        verifier: Box<dyn Verifier>,
        crypto_provider: CryptoProvider,
    ) -> anyhow::Result<Self> {
        let evidence = evidence_provider
            .get_evidence()
            .context("couldn't get evidence")?;

        verifier
            .verify(&evidence, &reference_value)
            .context("couldn't verify evidence")?;

        let encryptor = crypto_provider
            .get_encryptor(&evidence.enclave_public_key)
            .context("couldn't create encryptor")?;

        Ok(Self {
            transport,
            encryptor,
        })
    }

    pub async fn invoke(&mut self, request_body: &[u8]) -> anyhow::Result<Vec<u8>> {
        let (encrypted_request, decryptor) = self
            .encryptor
            .encrypt(request_body)
            .context("couldn't encrypt request")?;
        let encrypted_response = self
            .transport
            .invoke(&encrypted_request)
            .context("couldn't send request")?;
        let decrypted_response = decryptor
            .decrypt(&encrypted_response)
            .context("couldn't decrypt response")?;
        Ok(decrypted_response)
    }
}

// TODO(#3654): Implement client crypto provider.
pub struct CryptoProvider {}

impl CryptoProvider {
    fn get_encryptor(&self, _enclave_public_key: &[u8]) -> anyhow::Result<Encryptor> {
        Ok(Encryptor {})
    }
}

struct Encryptor {}

impl Encryptor {
    /// Returns the encrypted `message` and a corresponding `Decryptor` that should be used
    /// to decrypt the response message.
    fn encrypt(&mut self, _message: &[u8]) -> anyhow::Result<(Vec<u8>, Decryptor)> {
        Ok((vec![], Decryptor {}))
    }
}

struct Decryptor {}

impl Decryptor {
    fn decrypt(&self, _encrypted_message: &[u8]) -> anyhow::Result<Vec<u8>> {
        Ok(vec![])
    }
}
