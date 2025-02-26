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

use std::sync::Arc;

use anyhow::Context;
use oak_crypto::{encryption_key::AsyncEncryptionKeyHandle, hpke::RecipientContext};
use oak_grpc::oak::containers::v1::orchestrator_crypto_client::OrchestratorCryptoClient as GrpcOrchestratorCryptoClient;
use oak_proto_rust::oak::{
    containers::v1::{BindSessionRequest, DeriveSessionKeysRequest, KeyOrigin, SignRequest},
    crypto::v1::{SessionKeys, Signature},
};
use oak_session::session_binding::SessionBinder;

const SESSION_BINDER_INFO_STRING: &str = "oak-session-binding-key";

struct OrchestratorCryptoClient {
    inner: GrpcOrchestratorCryptoClient<tonic::transport::channel::Channel>,
}

impl OrchestratorCryptoClient {
    fn create(channel: &tonic::transport::channel::Channel) -> Self {
        Self { inner: GrpcOrchestratorCryptoClient::new(channel.clone()) }
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

    #[allow(dead_code)]
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

    async fn bind_session(
        &self,
        transcript: &[u8],
        additional_data: &[u8],
    ) -> anyhow::Result<Signature> {
        self.inner
            // TODO(#4477): Remove unnecessary copies of the Orchestrator client.
            .clone()
            .bind_session(BindSessionRequest {
                transcript: transcript.to_vec(),
                additional_data: additional_data.to_vec(),
            })
            .await?
            .into_inner()
            .signature
            .context("session binding was not provided by the Orchestrator")
    }
}

pub struct InstanceEncryptionKeyHandle {
    orchestrator_crypto_client: OrchestratorCryptoClient,
}

impl InstanceEncryptionKeyHandle {
    pub fn create(orchestrator_channel: &tonic::transport::Channel) -> Self {
        Self { orchestrator_crypto_client: OrchestratorCryptoClient::create(orchestrator_channel) }
    }
}

#[async_trait::async_trait]
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

#[derive(Clone)]
pub struct InstanceSessionBinder {
    orchestrator_crypto_client: Arc<OrchestratorCryptoClient>,
}

impl InstanceSessionBinder {
    pub fn create(orchestrator_channel: &tonic::transport::Channel) -> Self {
        Self {
            orchestrator_crypto_client: Arc::new(OrchestratorCryptoClient::create(
                orchestrator_channel,
            )),
        }
    }

    async fn bind_session(&self, transcript: &[u8]) -> anyhow::Result<Signature> {
        self.orchestrator_crypto_client
            .bind_session(transcript, SESSION_BINDER_INFO_STRING.as_bytes())
            .await
    }
}

// TODO: b/397193509 - Use `async` in the Session SDK.
impl SessionBinder for InstanceSessionBinder {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        tokio::runtime::Handle::current()
            .block_on(self.bind_session(bound_data))
            // Since there's no way to return the error, logging and returning an empty response is
            // preferable to panicking.
            .inspect_err(|err| {
                log::error!("OrchestratorCryptoClient session binding failed: {:?}", err)
            })
            .unwrap_or_default()
            .signature
    }
}
