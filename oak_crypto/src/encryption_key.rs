//
// Copyright 2024 The Project Oak Authors
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

use alloc::{boxed::Box, vec::Vec};

use anyhow::Context;
use async_trait::async_trait;
use oak_proto_rust::oak::crypto::v1::EncryptedRequest;
use zeroize::{Zeroize, Zeroizing};

use crate::{
    EMPTY_ASSOCIATED_DATA,
    encryptor::ClientEncryptor,
    hpke::{
        Deserializable, OAK_HPKE_INFO, PrivateKey, RecipientContext, Serializable,
        generate_kem_key_pair, setup_base_recipient,
    },
};

/// Generates a random encryption key pair and returns an instance of the
/// `EncryptionKey` and a NIST P-256 SEC1 encoded point public key.
/// <https://secg.org/sec1-v2.pdf>
pub fn generate_encryption_key_pair() -> (EncryptionKey, Vec<u8>) {
    let (private_key, public_key) = generate_kem_key_pair();
    (EncryptionKey::new(private_key), public_key.to_bytes().to_vec())
}

#[derive(Clone)]
pub struct EncryptionKey {
    private_key: PrivateKey,
}

impl EncryptionKey {
    pub fn new(private_key: PrivateKey) -> Self {
        Self { private_key }
    }

    pub fn serialize(self) -> Vec<u8> {
        self.private_key.to_bytes().to_vec()
    }

    pub fn deserialize(serialized_private_key: &mut [u8]) -> anyhow::Result<Self> {
        let private_key = PrivateKey::from_bytes(serialized_private_key)
            .map_err(|error| anyhow::anyhow!("couldn't deserialize private key: {}", error))?;
        serialized_private_key.zeroize();
        Ok(Self { private_key })
    }

    /// Returns the private key encrypted with the `peer_public_key`.
    pub fn encrypted_private_key(
        &self,
        peer_public_key: &[u8],
    ) -> anyhow::Result<EncryptedRequest> {
        let mut client_encryptor =
            ClientEncryptor::create(peer_public_key).context("creating client encryptor")?;
        client_encryptor
            .encrypt(&Zeroizing::new(self.private_key.to_bytes()), EMPTY_ASSOCIATED_DATA)
    }
}

/// Exposes the ability to derive a session key from the provided encapsulated
/// private key, using a private key that has been endorsed in the Attestation
/// Evidence.
pub trait EncryptionKeyHandle {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext>;
}

impl EncryptionKeyHandle for EncryptionKey {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        setup_base_recipient(encapsulated_public_key, &self.private_key, OAK_HPKE_INFO)
            .context("setting up base recipient")
    }
}

#[async_trait]
pub trait AsyncEncryptionKeyHandle {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext>;
}

#[async_trait]
impl AsyncEncryptionKeyHandle for EncryptionKey {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        (self as &dyn EncryptionKeyHandle).generate_recipient_context(encapsulated_public_key)
    }
}
