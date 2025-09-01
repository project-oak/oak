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

use anyhow::{Context, Result};
use futures::channel::mpsc::{self, Sender};
use oak_attestation_gcp::{
    policy_generator::confidential_space_policy_from_reference_values,
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use oak_attestation_verification::EventLogVerifier;
use oak_gcp_echo_proto::oak::standalone::example::enclave_application_client::EnclaveApplicationClient;
use oak_proto_rust::oak::{
    attestation::v1::{
        confidential_space_reference_values::ContainerImage, ConfidentialSpaceReferenceValues,
        CosignReferenceValues,
    },
    session::v1::{SessionRequest, SessionResponse},
};
use oak_proto_rust_lib::p256_ecdsa_verifying_key_to_proto;
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    key_extractor::DefaultBindingKeyExtractor,
    session::AttestationEvidence,
    ClientSession, Session,
};
use oak_time::Clock;
use p256::{ecdsa::VerifyingKey, pkcs8::DecodePublicKey};
use sigstore::rekor::REKOR_PUBLIC_KEY_PEM;
use tonic::transport::{Channel, Uri};

const ATTESTATION_ID: &str = "c0bbb3a6-2256-4390-a342-507b6aecb7e1";

// A client for streaming requests to the Echo server over an E2EE Noise
// Protocol session.
pub struct EchoClient {
    client_session: ClientSession,
    response_stream: tonic::codec::Streaming<SessionResponse>,
    tx: Sender<SessionRequest>,
}

impl EchoClient {
    pub async fn create<T: AsRef<str>>(
        url: T,
        clock: Arc<dyn Clock>,
        developer_public_key: VerifyingKey,
    ) -> Result<EchoClient> {
        let url = url.as_ref().to_owned();
        let uri = Uri::from_maybe_shared(url).context("invalid URI")?;
        let channel =
            Channel::builder(uri).connect().await.context("couldn't connect via gRPC channel")?;

        let mut client = EnclaveApplicationClient::new(channel);

        let (mut tx, rx) = mpsc::channel(10);

        let mut response_stream =
            client.oak_session(rx).await.context("couldn't send stream request")?.into_inner();

        // We don't have a noise client impl yet, so we need to manage the session
        // manually.
        let rekor_public_key = VerifyingKey::from_public_key_pem(REKOR_PUBLIC_KEY_PEM)
            .map_err(|e| anyhow::anyhow!("failed to parse rekor public key: {}", e))?;

        let reference_values = ConfidentialSpaceReferenceValues {
            root_certificate_pem: CONFIDENTIAL_SPACE_ROOT_CERT_PEM.to_owned(),
            r#container_image: Some(ContainerImage::CosignReferenceValues(CosignReferenceValues {
                developer_public_key: Some(p256_ecdsa_verifying_key_to_proto(
                    &developer_public_key,
                )),
                rekor_public_key: Some(p256_ecdsa_verifying_key_to_proto(&rekor_public_key)),
            })),
        };
        let policy = confidential_space_policy_from_reference_values(&reference_values)?;
        let attestation_verifier = EventLogVerifier::new(vec![Box::new(policy)], clock.clone());

        let client_config: SessionConfig =
            SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
                .add_peer_verifier_with_key_extractor(
                    ATTESTATION_ID.to_string(),
                    Box::new(attestation_verifier),
                    Box::new(DefaultBindingKeyExtractor {}),
                )
                .build();
        let mut client_session =
            ClientSession::create(client_config).expect("Failed to create client session");

        while !client_session.is_open() {
            let request = client_session.next_init_message().expect("expected client init message");
            tx.try_send(request).expect("failed to send to server");
            if !client_session.is_open() {
                let response = response_stream
                    .message()
                    .await
                    .expect("expected a response")
                    .expect("response was failure");
                client_session
                    .handle_init_message(response)
                    .expect("failed to handle init response");
            }
        }

        Ok(EchoClient { client_session, response_stream, tx })
    }

    pub async fn echo(&mut self, request: &[u8]) -> Result<Vec<u8>> {
        let request = self.client_session.encrypt(request).context("failed to encrypt message")?;

        self.tx.try_send(request).context("couldn't send request to server")?;

        let response = self
            .response_stream
            .message()
            .await
            .context("error getting response")?
            .context("didn't get any response")?;

        self.client_session.decrypt(response).context("failed to decrypt response")
    }

    pub fn get_peer_attestation_evidence(&self) -> Result<AttestationEvidence> {
        self.client_session.get_peer_attestation_evidence()
    }
}
