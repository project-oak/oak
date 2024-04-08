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

//! Structs for signing and encryption using keys attested in the instance's
//! attestation evidence.

use oak_crypto::{
    encryption_key::{EncryptionKey, EncryptionKeyHandle},
    hpke::RecipientContext,
};
use oak_proto_rust::oak::crypto::v1::Signature;
use p256::ecdsa::SigningKey;

/// [`EncryptionKeyHandle`] implementation that using the instance's evidence
/// and corresponding private keys.
#[derive(Clone)]
pub struct InstanceEncryptionKeyHandle {
    key: &'static EncryptionKey,
}

impl InstanceEncryptionKeyHandle {
    pub fn create() -> anyhow::Result<Self> {
        crate::attestation::DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .map(|d| InstanceEncryptionKeyHandle { key: &d.encryption_key })
    }
}

impl EncryptionKeyHandle for InstanceEncryptionKeyHandle {
    fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.key.generate_recipient_context(encapsulated_public_key)
    }
}

/// Exposes the ability to sign bytestrings using a private key that has been
/// endorsed in the Attestation Evidence.
pub trait Signer {
    /// Attempt to sign the provided message bytestring using a signing private
    /// key, a corresponding public key of which is contained in the
    /// Attestation Evidence.
    fn sign(&self, message: &[u8]) -> anyhow::Result<Signature>;
}

/// [`Signer`] implementation that using the instance's evidence and
/// corresponding private keys.
#[derive(Clone)]
pub struct InstanceSigner {
    key: &'static SigningKey,
}

impl InstanceSigner {
    pub fn create() -> anyhow::Result<Self> {
        crate::attestation::DICE_WRAPPER
            .as_ref()
            .map_err(anyhow::Error::msg)
            .map(|d| InstanceSigner { key: &d.signing_key })
    }
}

impl Signer for InstanceSigner {
    fn sign(&self, message: &[u8]) -> anyhow::Result<Signature> {
        Ok(<SigningKey as oak_crypto::signer::Signer>::sign(self.key, message))
    }
}
