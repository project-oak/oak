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

use anyhow::Context;
use async_trait::async_trait;
use oak_crypto::{encryption_key::AsyncEncryptionKeyHandle, hpke::RecipientContext};
use oak_proto_rust::oak::crypto::v1::{SessionKeys, Signature};
use tonic::transport::{Endpoint, Uri};
use tower::service_fn;

use crate::{
    proto::oak::containers::v1::{
        orchestrator_crypto_client::OrchestratorCryptoClient as GrpcOrchestratorCryptoClient,
        DeriveSessionKeysRequest, KeyOrigin, SignRequest,
    },
    IGNORED_ENDPOINT_URI, ORCHESTRATOR_IPC_SOCKET,
};

struct OrchestratorCryptoClient {
    inner: GrpcOrchestratorCryptoClient<tonic::transport::channel::Channel>,
}

impl OrchestratorCryptoClient {
    async fn create() -> anyhow::Result<Self> {
        let inner: GrpcOrchestratorCryptoClient<tonic::transport::channel::Channel> = {
            let channel = Endpoint::try_from(IGNORED_ENDPOINT_URI)
                .context("couldn't form endpoint")?
                .connect_with_connector(service_fn(move |_: Uri| {
                    tokio::net::UnixStream::connect(ORCHESTRATOR_IPC_SOCKET)
                }))
                .await
                .context("couldn't connect to UDS socket")?;

            GrpcOrchestratorCryptoClient::new(channel)
        };
        Ok(Self { inner })
    }

    async fn derive_session_keys(
        &self,
        key_origin: KeyOrigin,
        serialized_encapsulated_public_key: &[u8],
    ) -> Result<SessionKeys, Box<dyn std::error::Error>> {
        let context = self
            .inner
            // TODO(#4477): Remove unnecessary copies of the Orchestrator client.
            .clone()
            .derive_session_keys(DeriveSessionKeysRequest {
                key_origin: key_origin.into(),
                serialized_encapsulated_public_key: serialized_encapsulated_public_key.to_vec(),
            })
            .await?
            .into_inner()
            .session_keys
            .context("session keys weren't provided by the Orchestrator")?;
        Ok(context)
    }

    async fn sign(&self, key_origin: KeyOrigin, message: Vec<u8>) -> anyhow::Result<Signature> {
        self.inner
            // TODO(#4477): Remove unnecessary copies of the Orchestrator client.
            .clone()
            .sign(SignRequest { message, key_origin: key_origin.into() })
            .await?
            .into_inner()
            .signature
            .context("signature was not provided by the Orchestrator")
    }
}

pub struct InstanceEncryptionKeyHandle {
    orchestrator_crypto_client: OrchestratorCryptoClient,
}

impl InstanceEncryptionKeyHandle {
    pub async fn create() -> anyhow::Result<Self> {
        Ok(Self {
            orchestrator_crypto_client: OrchestratorCryptoClient::create()
                .await
                .context("couldn't create Orchestrator crypto client")?,
        })
    }
}

#[async_trait]
impl AsyncEncryptionKeyHandle for InstanceEncryptionKeyHandle {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        let serialized_crypto_context = self
            .orchestrator_crypto_client
            .derive_session_keys(KeyOrigin::Instance, encapsulated_public_key)
            .await
            .map_err(|error| {
                tonic::Status::internal(format!(
                    "couldn't get crypto context from the Orchestrator: {:?}",
                    error
                ))
            })?;
        let crypto_context =
            RecipientContext::deserialize(serialized_crypto_context).map_err(|error| {
                tonic::Status::internal(format!("couldn't deserialize crypto context: {:?}", error))
            })?;
        Ok(crypto_context)
    }
}

#[async_trait(?Send)]
pub trait Signer {
    async fn sign(&self, message: &[u8]) -> anyhow::Result<Signature>;
}

pub struct InstanceSigner {
    orchestrator_crypto_client: OrchestratorCryptoClient,
}

impl InstanceSigner {
    pub async fn create() -> anyhow::Result<Self> {
        Ok(Self {
            orchestrator_crypto_client: OrchestratorCryptoClient::create()
                .await
                .context("couldn't create Orchestrator crypto client")?,
        })
    }
}

#[async_trait(?Send)]
impl Signer for InstanceSigner {
    async fn sign(&self, message: &[u8]) -> anyhow::Result<Signature> {
        self.orchestrator_crypto_client.sign(KeyOrigin::Instance, message.to_vec()).await
    }
}
