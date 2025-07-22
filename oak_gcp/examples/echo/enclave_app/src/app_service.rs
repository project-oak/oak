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

/// App service shows an example of the boilerplate needed to implement the
/// Oak-related machinery for session message stream handling.
///
/// Oak doesn't provide full service implementation conveniences in the SDK,
/// since typically, Oak-enabled methods will be part of a larger service that
/// may need to be configured in specific ways.
use std::{pin::Pin, sync::Arc};

use anyhow::anyhow;
use oak_attestation::public_key::{PublicKeyAttester, PublicKeyEndorser};
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_gcp_echo_proto::oak::standalone::example::enclave_application_server::{
    EnclaveApplication, EnclaveApplicationServer,
};
use oak_proto_rust::oak::{
    attestation::v1::ConfidentialSpaceEndorsement,
    session::v1::{SessionRequest, SessionResponse},
};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    session_binding::{SessionBinder, SignatureBinder},
    ServerSession, Session,
};
use p256::ecdsa::{SigningKey, VerifyingKey};
use tokio::net::TcpListener;
use tokio_stream::{wrappers::TcpListenerStream, Stream, StreamExt};

use crate::app::EchoHandler;

const ATTESTATION_ID: &str = "c0bbb3a6-2256-4390-a342-507b6aecb7e1";

/// Holds the gRPC EnclaveApplication implementation.
pub struct EnclaveApplicationImplementation {
    application_handler: Arc<EchoHandler>,
    attester: Arc<dyn Attester>,
    endorser: Arc<dyn Endorser>,
    session_binder: Arc<dyn SessionBinder>,
}

impl EnclaveApplicationImplementation {
    pub fn new(
        application_handler: EchoHandler,
        binding_key: SigningKey,
        endorsement: ConfidentialSpaceEndorsement,
    ) -> Self {
        Self {
            application_handler: Arc::new(application_handler),
            attester: Arc::new(PublicKeyAttester::new(VerifyingKey::from(&binding_key))),
            endorser: Arc::new(PublicKeyEndorser::new(endorsement)),
            session_binder: Arc::new(SignatureBinder::new(Box::new(binding_key))),
        }
    }
}

trait IntoTonicResult<T> {
    #[allow(clippy::result_large_err)]
    fn into_tonic_result(self, context: &str) -> tonic::Result<T>;
}

impl<T> IntoTonicResult<T> for anyhow::Result<T> {
    fn into_tonic_result(self, context: &str) -> tonic::Result<T> {
        self.map_err(|e| tonic::Status::internal(format!("{context}: {e:?}")))
    }
}

#[tonic::async_trait]
impl EnclaveApplication for EnclaveApplicationImplementation {
    type OakSessionStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;

    async fn oak_session(
        &self,
        request: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::OakSessionStream>, tonic::Status> {
        let mut server_session = ServerSession::create(
            SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
                .add_self_attester_ref(ATTESTATION_ID.to_owned(), &self.attester)
                .add_self_endorser_ref(ATTESTATION_ID.to_owned(), &self.endorser)
                .add_session_binder_ref(ATTESTATION_ID.to_owned(), &self.session_binder)
                .build(),
        )
        .map_err(|e| tonic::Status::internal(format!("could not create server session: {e:?}")))?;

        let application_handler = self.application_handler.clone();

        let mut request_stream = request.into_inner();
        // TODO: b/381532760 - Consolidate Noise-related boilerplate into the SDK.
        let response_stream = async_stream::try_stream! {
            while let Some(request) = request_stream.next().await {
                let session_request = request?;
                if server_session.is_open() {
                    let decrypted_request = server_session.decrypt(session_request)
                        .into_tonic_result("failed to decrypt request")?;
                    let plaintext_response = application_handler.handle(&decrypted_request).await
                        .into_tonic_result("application failed")?;
                    yield server_session.encrypt(plaintext_response)
                        .into_tonic_result("failed to encrypt response")?;

                } else {
                    server_session.handle_init_message(session_request).into_tonic_result("failed to handle init request")?;
                    if !server_session.is_open() {
                        yield server_session.next_init_message().into_tonic_result("failed to get init response")?;
                    }
                }
            }
        };
        Ok(tonic::Response::new(Box::pin(response_stream) as Self::OakSessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    application_handler: EchoHandler,
    binding_key: SigningKey,
    endorsement: ConfidentialSpaceEndorsement,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(EnclaveApplicationServer::new(EnclaveApplicationImplementation::new(
            application_handler,
            binding_key,
            endorsement,
        )))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
