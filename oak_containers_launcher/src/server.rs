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

use crate::proto::oak::{
    containers::{
        launcher_server::{Launcher, LauncherServer},
        GetApplicationConfigResponse, GetImageResponse, LogEntry, SendAttestationEvidenceRequest,
    },
    session::v1::AttestationEvidence,
};
use anyhow::anyhow;
use futures::{FutureExt, Stream, StreamExt};
use opentelemetry_proto::tonic::collector::metrics::v1::{
    metrics_service_server::{MetricsService, MetricsServiceServer},
    ExportMetricsServiceRequest, ExportMetricsServiceResponse,
};
use std::{pin::Pin, sync::Mutex};
use tokio::{
    io::{AsyncReadExt, BufReader},
    net::TcpListener,
    sync::oneshot::{Receiver, Sender},
};
use tokio_stream::wrappers::TcpListenerStream;
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
    // Will be used to send the Attestation Evidence to the Launcher.
    attestation_evidence_sender: Mutex<Option<Sender<AttestationEvidence>>>,
    // Will be used to notify the untrusted application that the trusted application is ready and
    // listening on a socket address.
    app_ready_notifier: Mutex<Option<Sender<()>>>,
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
        self.attestation_evidence_sender
            .lock()
            .map_err(|err| {
                tonic::Status::internal(format!(
                    "couldn't get exclusive access to attestation evidence sender: {err}"
                ))
            })?
            .take()
            .ok_or_else(|| {
                tonic::Status::invalid_argument("app has already sent an attestation evidence")
            })?
            .send(request.into_inner().evidence.unwrap_or_default())
            .map_err(|_err| {
                tonic::Status::internal(format!("couldn't send attestation evidence"))
            })?;
        Ok(tonic::Response::new(()))
    }

    async fn notify_app_ready(&self, _request: Request<()>) -> Result<Response<()>, tonic::Status> {
        self.app_ready_notifier
            .lock()
            .map_err(|err| {
                tonic::Status::internal(format!(
                    "couldn't get exclusive access to notification channel: {err}"
                ))
            })?
            .take()
            .ok_or_else(|| {
                tonic::Status::invalid_argument("app has already sent a ready notification")
            })?
            .send(())
            .map_err(|_err| tonic::Status::internal(format!("couldn't send notification")))?;
        Ok(tonic::Response::new(()))
    }

    async fn log(
        &self,
        request: Request<tonic::Streaming<LogEntry>>,
    ) -> Result<Response<()>, tonic::Status> {
        let mut stream = request.into_inner();
        while let Some(message) = stream.next().await {
            let message = message?;

            let unit = message
                .fields
                .get("_SYSTEMD_UNIT")
                .map_or("", |unit| unit.as_str());
            let message = message
                .fields
                .get("MESSAGE")
                .map_or("", |message| message.as_str());
            println!("{}: {}", unit, message);
        }
        Ok(tonic::Response::new(()))
    }
}

struct LogServer;

#[tonic::async_trait]
impl MetricsService for LogServer {
    async fn export(
        &self,
        request: Request<ExportMetricsServiceRequest>,
    ) -> Result<Response<ExportMetricsServiceResponse>, tonic::Status> {
        let request = request.into_inner();
        log::debug!("metrics: {:?}", request);
        Ok(Response::new(ExportMetricsServiceResponse {
            partial_success: None,
        }))
    }
}

pub async fn new(
    listener: TcpListener,
    system_image: std::path::PathBuf,
    container_bundle: std::path::PathBuf,
    application_config: Option<std::path::PathBuf>,
    attestation_evidence_sender: Sender<AttestationEvidence>,
    app_ready_notifier: Sender<()>,
    shutdown: Receiver<()>,
) -> Result<(), anyhow::Error> {
    let server_impl = LauncherServerImplementation {
        system_image,
        container_bundle,
        application_config,
        attestation_evidence_sender: Mutex::new(Some(attestation_evidence_sender)),
        app_ready_notifier: Mutex::new(Some(app_ready_notifier)),
    };
    Server::builder()
        .add_service(LauncherServer::new(server_impl))
        .add_service(MetricsServiceServer::new(LogServer))
        .serve_with_incoming_shutdown(TcpListenerStream::new(listener), shutdown.map(|_| ()))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
