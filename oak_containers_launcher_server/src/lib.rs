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

mod proto {
    pub mod oak {
        pub mod containers {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers");
        }
        pub mod session {
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                tonic::include_proto!("oak.session.v1");
            }
        }
    }
}

use self::proto::oak::{
    containers::{
        launcher_server::{Launcher, LauncherServer},
        GetApplicationConfigResponse, GetImageResponse, SendAttestationEvidenceRequest,
    },
    session::v1::AttestationEvidence,
};
use anyhow::anyhow;
use futures::Stream;
use std::{pin::Pin, sync::Mutex};
use tokio::io::{AsyncReadExt, BufReader};
use tokio_vsock::VsockListener;
use tonic::{transport::Server, Request, Response, Status};

// Most gRPC implementations limit message sizes to 4MiB. Let's stay
// comfortably below that by limiting responses to 3MiB.
const MAX_RESPONSE_SIZE: usize = 3 * 1024 * 1024;

type GetImageResponseStream = Pin<Box<dyn Stream<Item = Result<GetImageResponse, Status>> + Send>>;

#[derive(Default)]
struct LauncherServerImplementation {
    system_image: std::path::PathBuf,
    container_bundle: std::path::PathBuf,
    application_config: Option<std::path::PathBuf>,
    // Attestation Evidence is initialized by the Orchestrator.
    attestation_evidence: Mutex<Option<AttestationEvidence>>,
}

#[tonic::async_trait]
impl Launcher for LauncherServerImplementation {
    type GetOakSystemImageStream = GetImageResponseStream;
    type GetContainerBundleStream = GetImageResponseStream;

    async fn get_oak_system_image(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Self::GetOakSystemImageStream>, tonic::Status> {
        let system_image_file = tokio::fs::File::open(&self.system_image).await?;

        let mut buffer = vec![0_u8; MAX_RESPONSE_SIZE];
        let mut reader = BufReader::new(system_image_file);

        let response_stream = async_stream::try_stream! {
            loop {
                let bytes_read = reader.read(&mut buffer).await?;

                if bytes_read > 0 {
                    yield GetImageResponse {
                        image_chunk: buffer[..bytes_read].to_vec()
                    }
                } else {
                    // the file has been fully read, there's nothing left to
                    // send
                    break;
                }
            }
        };

        Ok(Response::new(
            Box::pin(response_stream) as Self::GetOakSystemImageStream
        ))
    }

    async fn get_container_bundle(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Self::GetContainerBundleStream>, tonic::Status> {
        let container_bundle_file = tokio::fs::File::open(&self.container_bundle).await?;

        let mut buffer = vec![0_u8; MAX_RESPONSE_SIZE];
        let mut reader = BufReader::new(container_bundle_file);

        let response_stream = async_stream::try_stream! {
            loop {
                let bytes_read = reader.read(&mut buffer).await?;

                if bytes_read > 0 {
                    yield GetImageResponse {
                        image_chunk: buffer[..bytes_read].to_vec()
                    }
                } else {
                    // the file has been fully read, there's nothing left to
                    // send
                    break;
                }
            }
        };

        Ok(Response::new(
            Box::pin(response_stream) as Self::GetContainerBundleStream
        ))
    }

    async fn get_application_config(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetApplicationConfigResponse>, tonic::Status> {
        match &self.application_config {
            Some(config_path) => {
                let application_config_file = tokio::fs::File::open(&config_path).await?;
                let mut buffer = Vec::new();
                let mut reader = BufReader::new(application_config_file);
                reader.read_to_end(&mut buffer).await?;
                Ok(tonic::Response::new(GetApplicationConfigResponse {
                    config: buffer,
                }))
            }
            None => Ok(tonic::Response::new(GetApplicationConfigResponse::default())),
        }
    }

    async fn send_attestation_evidence(
        &self,
        request: Request<SendAttestationEvidenceRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        let mut attestation_evidence = self.attestation_evidence.lock().map_err(|err| {
            tonic::Status::internal(format!("couldn't access attestation evidence: {err}"))
        })?;
        match *attestation_evidence {
            Some(_) => Err(tonic::Status::invalid_argument(
                "attestation evidence has already been sent to the Launcher",
            )),
            None => {
                *attestation_evidence = request.into_inner().evidence;
                Ok(tonic::Response::new(()))
            }
        }
    }
}

pub async fn new(
    vsock_cid: u32,
    vsock_port: u32,
    system_image: std::path::PathBuf,
    container_bundle: std::path::PathBuf,
    application_config: Option<std::path::PathBuf>,
) -> Result<(), anyhow::Error> {
    let server_impl = LauncherServerImplementation {
        system_image,
        container_bundle,
        application_config,
        // Attestation Evidence will be sent by the Orchestrator once generated.
        attestation_evidence: Mutex::new(None),
    };
    let vsock_listener = VsockListener::bind(vsock_cid, vsock_port)?.incoming();

    Server::builder()
        .add_service(LauncherServer::new(server_impl))
        .serve_with_incoming(vsock_listener)
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
