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

use alloc::{boxed::Box, vec::Vec};

use anyhow::Context;
use oak_crypto::{
    encryption_key::{EncryptionKey, EncryptionKeyHandle},
    hpke::RecipientContext,
    signer::Signer,
};
use oak_session::session_binding::{SessionBinder, SignatureBinder, SignatureBinderBuilder};
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
    fn sign(&self, message: &[u8]) -> Vec<u8> {
        <SigningKey as oak_crypto::signer::Signer>::sign(self.key, message)
    }
}

pub struct InstanceSessionBinder {
    signature_binder: SignatureBinder,
}

impl InstanceSessionBinder {
    pub fn create() -> anyhow::Result<Self> {
        // TODO: b/368030563 - Add a separate session binding key and use it instead
        // of signing key.
        let signer = InstanceSigner::create().context("couldn't get binding key")?;

        let signature_binder = SignatureBinderBuilder::default()
            .signer(Box::new(signer))
            .build()
            .map_err(anyhow::Error::msg)?;
        Ok(Self { signature_binder })
    }
}

impl SessionBinder for InstanceSessionBinder {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        self.signature_binder.bind(bound_data)
    }
}
