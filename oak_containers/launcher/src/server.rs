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

use std::{
    pin::Pin,
    sync::{Arc, Mutex},
};

use anyhow::anyhow;
use bytes::BytesMut;
use futures::{FutureExt, Stream};
use oak_grpc::oak::containers::{
    launcher_server::{Launcher, LauncherServer},
    v1::hostlib_key_provisioning_server::{HostlibKeyProvisioning, HostlibKeyProvisioningServer},
};
use oak_proto_rust::oak::{
    attestation::v1::{Endorsements, Evidence},
    containers::{
        GetApplicationConfigResponse, GetImageResponse, SendAttestationEvidenceRequest,
        v1::{GetGroupKeysResponse, GetKeyProvisioningRoleResponse, KeyProvisioningRole},
    },
};
use opentelemetry_proto::tonic::{
    collector::{
        logs::v1::{
            ExportLogsServiceRequest, ExportLogsServiceResponse,
            logs_service_server::{LogsService, LogsServiceServer},
        },
        metrics::v1::{
            ExportMetricsServiceRequest, ExportMetricsServiceResponse,
            metrics_service_server::{MetricsService, MetricsServiceServer},
        },
    },
    common::v1::any_value::Value,
};
use tokio::{
    io::{AsyncReadExt, BufReader},
    net::TcpListener,
    sync::{oneshot, watch},
};
use tokio_stream::wrappers::TcpListenerStream;
use tokio_vsock::VsockListener;
use tonic::{Request, Response, Status, transport::Server};

// Most gRPC implementations limit message sizes to 4MiB. Let's stay
// comfortably below that by limiting responses to 3MiB.
const MAX_RESPONSE_SIZE: usize = 3 * 1024 * 1024;

type GetImageResponseStream = Pin<Box<dyn Stream<Item = Result<GetImageResponse, Status>> + Send>>;

#[derive(Default)]
struct LauncherServerImplementation {
    system_image: std::path::PathBuf,
    container_bundle: std::path::PathBuf,
    application_config: Vec<u8>,
    // Will be used to send the Attestation Evidence to the Launcher.
    evidence_sender: Mutex<Option<oneshot::Sender<Evidence>>>,
    // Will be used to notify the untrusted application that the trusted application is ready and
    // listening on a socket address.
    app_ready_notifier: Mutex<Option<oneshot::Sender<()>>>,
    endorsements: Endorsements,
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

        let mut reader = BufReader::new(system_image_file);

        let response_stream = async_stream::try_stream! {
            while let mut buffer = BytesMut::with_capacity(MAX_RESPONSE_SIZE) && reader.read_buf(&mut buffer).await? > 0 {
                yield GetImageResponse {
                    image_chunk: buffer.freeze()
                };
            }
        };

        Ok(Response::new(Box::pin(response_stream) as Self::GetOakSystemImageStream))
    }

    async fn get_container_bundle(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Self::GetContainerBundleStream>, tonic::Status> {
        let container_bundle_file = tokio::fs::File::open(&self.container_bundle).await?;

        let mut reader = BufReader::new(container_bundle_file);

        let response_stream = async_stream::try_stream! {
            while let mut buffer = BytesMut::with_capacity(MAX_RESPONSE_SIZE) && reader.read_buf(&mut buffer).await? > 0 {
                yield GetImageResponse {
                    image_chunk: buffer.freeze()
                };
            }
        };

        Ok(Response::new(Box::pin(response_stream) as Self::GetContainerBundleStream))
    }

    async fn get_application_config(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetApplicationConfigResponse>, tonic::Status> {
        Ok(tonic::Response::new(GetApplicationConfigResponse {
            config: self.application_config.clone(),
        }))
    }

    async fn send_attestation_evidence(
        &self,
        request: Request<SendAttestationEvidenceRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        let request = request.into_inner();
        let evidence = request.dice_evidence.ok_or_else(|| {
            tonic::Status::internal("send_attestation_evidence_request doesn't have evidence")
        })?;

        self.evidence_sender
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
            .send(evidence)
            .map_err(|_err| {
                tonic::Status::internal("couldn't send attestation evidence".to_string())
            })?;
        Ok(tonic::Response::new(()))
    }

    async fn get_endorsements(
        &self,
        _request: Request<()>,
    ) -> Result<Response<Endorsements>, tonic::Status> {
        Ok(tonic::Response::new(self.endorsements.clone()))
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
            .map_err(|_err| tonic::Status::internal("couldn't send notification".to_string()))?;
        Ok(tonic::Response::new(()))
    }
}

#[tonic::async_trait]
impl HostlibKeyProvisioning for LauncherServerImplementation {
    async fn get_key_provisioning_role(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetKeyProvisioningRoleResponse>, tonic::Status> {
        // TODO(#4442): Implement setting Hostlib Key Provisioning role via an input
        // argument.
        Ok(tonic::Response::new(GetKeyProvisioningRoleResponse {
            role: KeyProvisioningRole::Leader.into(),
        }))
    }

    async fn get_group_keys(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetGroupKeysResponse>, tonic::Status> {
        // TODO(#4442): Implement sending group keys to the orchestrator.
        Err(tonic::Status::unimplemented("Key Provisioning is not implemented"))
    }
}

#[tonic::async_trait]
impl MetricsService for LauncherServerImplementation {
    async fn export(
        &self,
        request: Request<ExportMetricsServiceRequest>,
    ) -> Result<Response<ExportMetricsServiceResponse>, tonic::Status> {
        let request = request.into_inner();
        log::debug!("metrics: {:?}", request);
        Ok(Response::new(ExportMetricsServiceResponse { partial_success: None }))
    }
}

#[tonic::async_trait]
impl LogsService for LauncherServerImplementation {
    async fn export(
        &self,
        request: Request<ExportLogsServiceRequest>,
    ) -> Result<Response<ExportLogsServiceResponse>, tonic::Status> {
        let request = request.into_inner();
        for resource_log in &request.resource_logs {
            for scope_log in &resource_log.scope_logs {
                for log_record in &scope_log.log_records {
                    let unit = log_record
                        .attributes
                        .iter()
                        .find_map(
                            |x| if x.key == "_SYSTEMD_UNIT" { x.value.as_ref() } else { None },
                        )
                        .and_then(|value| value.value.as_ref())
                        .and_then(|value| match value {
                            Value::StringValue(x) => Some(x.as_str()),
                            _ => None,
                        })
                        .unwrap_or_default();
                    let body = log_record
                        .body
                        .as_ref()
                        .and_then(|body| body.value.as_ref())
                        .and_then(|value| match value {
                            Value::StringValue(x) => Some(x.as_str()),
                            _ => None,
                        })
                        .unwrap_or_default();
                    println!("{}: {}", unit, body);
                }
            }
        }

        Ok(Response::new(ExportLogsServiceResponse { partial_success: None }))
    }
}

// Clippy is not wrong, but hopefully the situation with two listeners is only
// temporary.
#[allow(clippy::too_many_arguments)]
pub async fn new(
    listener: TcpListener,
    vsock_listener: VsockListener,
    system_image: std::path::PathBuf,
    container_bundle: std::path::PathBuf,
    application_config: Vec<u8>,
    evidence_sender: oneshot::Sender<Evidence>,
    app_ready_notifier: oneshot::Sender<()>,
    shutdown: watch::Receiver<()>,
    endorsements: Endorsements,
) -> Result<(), anyhow::Error> {
    let server_impl = Arc::new(LauncherServerImplementation {
        system_image,
        container_bundle,
        application_config,
        evidence_sender: Mutex::new(Some(evidence_sender)),
        app_ready_notifier: Mutex::new(Some(app_ready_notifier)),
        endorsements,
    });

    let mut tcp_shutdown = shutdown.clone();
    let tcp_server = Server::builder()
        .add_service(LauncherServer::from_arc(server_impl.clone()))
        .add_service(HostlibKeyProvisioningServer::from_arc(server_impl.clone()))
        .add_service(MetricsServiceServer::from_arc(server_impl.clone()))
        .add_service(LogsServiceServer::from_arc(server_impl.clone()))
        .serve_with_incoming_shutdown(
            TcpListenerStream::new(listener),
            tcp_shutdown.changed().map(|_| ()),
        );

    let mut virtio_shutdown = shutdown.clone();
    let virtio_server = Server::builder()
        .add_service(LauncherServer::from_arc(server_impl.clone()))
        .add_service(HostlibKeyProvisioningServer::from_arc(server_impl.clone()))
        .serve_with_incoming_shutdown(
            vsock_listener.incoming(),
            virtio_shutdown.changed().map(|_| ()),
        );

    tokio::try_join!(tcp_server, virtio_server)
        .map(|((), ())| ())
        .map_err(|error| anyhow!("server error: {:?}", error))
}
