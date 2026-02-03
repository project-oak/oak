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
use std::{collections::BTreeMap, pin::Pin, sync::Arc};

use anyhow::{Context, Result, anyhow};
use oak_attestation_gcp::{OAK_SESSION_NOISE_V1_AUDIENCE, assertions::GcpAssertionGenerator};
use oak_gcp_echo_proto::oak::standalone::example::enclave_application_server::{
    EnclaveApplication, EnclaveApplicationServer,
};
use oak_proto_rust::oak::{
    attestation::v1::ConfidentialSpaceEndorsement,
    session::v1::{SessionRequest, SessionResponse},
};
use oak_session::{
    ServerSession, Session,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    generator::{BindableAssertionGenerator, SessionKeyBindableAssertionGenerator},
    handshake::HandshakeType,
};
use p256::ecdsa::SigningKey;
use tokio::net::TcpListener;
use tokio_stream::{Stream, StreamExt, wrappers::TcpListenerStream};

use crate::app::EchoHandler;

const ATTESTATION_ID: &str = "c0bbb3a6-2256-4390-a342-507b6aecb7e1";

/// Holds the gRPC EnclaveApplication implementation.
pub struct EnclaveApplicationImplementation {
    application_handler: Arc<EchoHandler>,
    assertion_generators: BTreeMap<String, Arc<dyn BindableAssertionGenerator>>,
}

impl EnclaveApplicationImplementation {
    pub fn new(
        application_handler: EchoHandler,
        binding_key: SigningKey,
        endorsement: ConfidentialSpaceEndorsement,
    ) -> Result<Self> {
        let gcp_assertion_generator: Arc<dyn BindableAssertionGenerator> = Arc::new(
            SessionKeyBindableAssertionGenerator::create_with_assertion_generator(
                &GcpAssertionGenerator {
                    audience: OAK_SESSION_NOISE_V1_AUDIENCE.to_string(),
                    endorsement: Some(endorsement),
                },
                Arc::new(binding_key),
            )
            .context("calling the GCP assertion generator")?,
        );
        Ok(Self {
            application_handler: Arc::new(application_handler),
            assertion_generators: BTreeMap::from([(
                ATTESTATION_ID.to_string(),
                gcp_assertion_generator,
            )]),
        })
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
        let mut session_config_builder =
            SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN);
        for (id, assertion_generator) in &self.assertion_generators {
            session_config_builder = session_config_builder
                .add_self_assertion_generator_ref(id.clone(), assertion_generator);
        }
        let mut server_session =
            ServerSession::create(session_config_builder.build()).map_err(|e| {
                tonic::Status::internal(format!("could not create server session: {e:#?}"))
            })?;

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
        )?))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
