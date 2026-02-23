//
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
//

//! This module provides a `SessionBinder` implementation for Oak Private Memory
//! that integrates with the Oak Containers Orchestrator.
//!
//! Handshake script signing in Oak Session needs to be non-blocking to ensure
//! efficient handshakes. However, signing directly via the Orchestrator
//! involves a blocking network call. To resolve this,
//! `OrchestratorSessionBinder` generates a local keypair at
//! initialization that persists for the lifetime of the workload. This local
//! public key is signed once by the Orchestrator. Subsequent session binding
//! operations (the `bind` method) then use this local keypair to sign the
//! bound data synchronously, without further network interaction.
//!
//! The final session binding data includes the local signature, the local
//! public key, and the Orchestrator's signature of that local public key,
//! allowing the counterparty to verify the entire chain of trust back to the
//! Orchestrator.

use anyhow::Context;
use async_trait::async_trait;
use oak_grpc::oak::containers::v1::orchestrator_crypto_client::OrchestratorCryptoClient as GrpcOrchestratorCryptoClient;
use oak_proto_rust::oak::containers::v1::{KeyOrigin, SignRequest};
use oak_session::session_binding::SessionBinder;
use p256::ecdsa::signature::Signer;
use prost::Message;
use rand_core::OsRng;
use sealed_memory_rust_proto::oak::private_memory::SessionBinding;

/// Trait representing an entity capable of signing messages using the
/// Orchestrator.
///
/// This abstraction allows for easier testing and mocking of the Orchestrator's
/// signing capability.
#[async_trait]
pub trait OrchestratorSigner: Send + Sync {
    /// Signs a message using the Orchestrator's key.
    async fn sign(&mut self, message: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// A wrapper around the gRPC Orchestrator Crypto Client that implements
/// `OrchestratorSigner`.
#[derive(Clone)]
pub struct OrchestratorClientWrapper {
    crypto_client: GrpcOrchestratorCryptoClient<tonic::transport::channel::Channel>,
}

impl OrchestratorClientWrapper {
    /// Creates a new `OrchestratorClientWrapper` using the provided gRPC
    /// channel.
    pub fn create(channel: &tonic::transport::channel::Channel) -> Self {
        Self { crypto_client: GrpcOrchestratorCryptoClient::new(channel.clone()) }
    }
}

#[async_trait]
impl OrchestratorSigner for OrchestratorClientWrapper {
    async fn sign(&mut self, message: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request =
            SignRequest { message: message.to_vec(), key_origin: KeyOrigin::Instance.into() };
        let response = self.crypto_client.sign(request).await?.into_inner();
        Ok(response.signature.context("signature was not provided by the Orchestrator")?.signature)
    }
}

/// A `SessionBinder` that uses a local keypair for non-blocking signing.
///
/// The keypair is generated once and used for the lifetime of the workload.
/// During creation, it generates a P-256 keypair and requests the Orchestrator
/// to sign the public key. This signature is stored and used in the `bind`
/// method to provide evidence of the local key's authenticity.
///
/// Note that the Orchestrator client or channel used during creation is not
/// persisted in this struct; it is only required for the initial setup.
#[derive(Clone)]
pub struct OrchestratorSessionBinder {
    /// The signing key generated locally.
    signing_key: p256::ecdsa::SigningKey,
    /// The Orchestrator's signature of the local public key.
    public_key_signature: Vec<u8>,
}

impl OrchestratorSessionBinder {
    /// Creates an `OrchestratorSessionBinder` by connecting to the Orchestrator
    /// via the provided channel.
    ///
    /// The channel is used only during this call to obtain the initial
    /// signature and is not stored.
    pub async fn create_from_channel(
        channel: &tonic::transport::channel::Channel,
    ) -> anyhow::Result<Self> {
        let orchestrator_client_wrapper = OrchestratorClientWrapper::create(channel);
        Self::create(orchestrator_client_wrapper).await
    }

    /// Creates an `OrchestratorSessionBinder` using the provided
    /// `OrchestratorSigner`.
    ///
    /// This method generates the local keypair and performs the one-time
    /// network call to get the Orchestrator's signature for the local
    /// public key. The `orchestrator_client` is not persisted.
    pub async fn create<C>(mut orchestrator_client: C) -> anyhow::Result<Self>
    where
        C: OrchestratorSigner,
    {
        let signing_key = p256::ecdsa::SigningKey::random(&mut OsRng);
        let public_key = signing_key.verifying_key().to_sec1_bytes().to_vec();
        let public_key_signature =
            orchestrator_client.sign(&public_key).await.context("failed to sign public key")?;
        Ok(Self { signing_key, public_key_signature })
    }
}

impl SessionBinder for OrchestratorSessionBinder {
    /// Binds data to the session using the local key.
    ///
    /// This method is non-blocking and synchronous. It returns an encoded
    /// `SessionBinding` containing the signature of the `bound_data`, the
    /// local public key, and the Orchestrator's signature of that public
    /// key.
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        let signature: p256::ecdsa::Signature = self.signing_key.sign(bound_data);
        let public_key = self.signing_key.verifying_key().to_sec1_bytes().to_vec();

        let binding = SessionBinding {
            signature: signature.to_bytes().to_vec(),
            public_key,
            public_key_signature: self.public_key_signature.clone(),
        };

        binding.encode_to_vec()
    }
}
