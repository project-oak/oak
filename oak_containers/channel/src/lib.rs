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
use hyper_util::rt::TokioIo;
use tokio_vsock::{VsockAddr, VsockStream, VMADDR_CID_HOST};
use tonic::transport::Channel;
use tower::service_fn;

pub mod buffer;

pub async fn create_channel(addr: tonic::transport::Uri) -> anyhow::Result<Channel> {
    if addr.scheme_str() == Some("vsock") {
        let vsock_addr = get_vsock_addr(addr)?;
        // The C++ gRPC implementations are more particular about the URI scheme; in
        // particular, they may get confused by the "vsock" scheme. Therefore, create a
        // fake URI with the "http" scheme to placate the libraries; the actual
        // connection is made in `connect_with_connector` and that uses the correct URI.
        let connector = service_fn(move |_| async move {
            Ok::<_, std::io::Error>(TokioIo::new(VsockStream::connect(vsock_addr).await?))
        });
        Ok(Channel::builder(tonic::transport::Uri::from_static("http://0:0"))
            .connect_with_connector(connector)
            .await?)
    } else {
        Ok(Channel::builder(addr.clone()).connect().await?)
    }
}

fn get_vsock_addr(addr: tonic::transport::Uri) -> anyhow::Result<VsockAddr> {
    // If there is no host, we assume VMADDR_CID_HOST.
    let cid = addr
        .host()
        .unwrap_or(format!("{}", VMADDR_CID_HOST).as_str())
        .parse::<u32>()
        .context("invalid vsock CID")?;
    let authority =
        addr.authority().context("failed to extract authority from vsock address")?.as_str();
    if !authority.contains(':') {
        anyhow::bail!("malformed vsock address");
    }
    Ok(VsockAddr::new(
        cid,
        authority
            .split(':')
            .next_back()
            .context("failed to extract port from vsock address")?
            .parse::<u32>()
            .context("invalid vsock port")?,
    ))
}

#[cfg(test)]
mod tests {
    use std::{
        net::{IpAddr, Ipv4Addr, SocketAddr},
        pin::Pin,
    };

    use futures::{FutureExt, Stream};
    use oak_grpc::oak::containers::{
        launcher_client::LauncherClient,
        launcher_server::{Launcher, LauncherServer},
    };
    use oak_proto_rust::oak::{
        attestation::v1::Endorsements,
        containers::{
            GetApplicationConfigResponse, GetImageResponse, SendAttestationEvidenceRequest,
        },
    };
    use tokio::net::TcpListener;
    use tokio_stream::wrappers::TcpListenerStream;
    #[cfg(feature = "vsock")]
    use tokio_vsock::{VsockListener, VMADDR_CID_LOCAL};
    use tonic::{Request, Response, Status};

    use super::*;

    struct TestLauncherServer {}

    type GetImageResponseStream =
        Pin<Box<dyn Stream<Item = Result<GetImageResponse, Status>> + Send>>;

    #[tonic::async_trait]
    impl Launcher for TestLauncherServer {
        type GetOakSystemImageStream = GetImageResponseStream;
        type GetContainerBundleStream = GetImageResponseStream;

        async fn get_oak_system_image(
            &self,
            _request: Request<()>,
        ) -> Result<Response<Self::GetOakSystemImageStream>, tonic::Status> {
            Err(tonic::Status::unimplemented("unimplemented"))
        }

        async fn get_container_bundle(
            &self,
            _request: Request<()>,
        ) -> Result<Response<Self::GetContainerBundleStream>, tonic::Status> {
            Err(tonic::Status::unimplemented("unimplemented"))
        }

        async fn get_application_config(
            &self,
            _request: Request<()>,
        ) -> Result<Response<GetApplicationConfigResponse>, tonic::Status> {
            Ok(tonic::Response::new(GetApplicationConfigResponse {
                config: b"oak_application_config".to_vec(),
            }))
        }

        async fn get_endorsements(
            &self,
            _request: Request<()>,
        ) -> Result<Response<Endorsements>, tonic::Status> {
            Err(tonic::Status::unimplemented("unimplemented"))
        }

        async fn send_attestation_evidence(
            &self,
            _request: Request<SendAttestationEvidenceRequest>,
        ) -> Result<Response<()>, tonic::Status> {
            Err(tonic::Status::unimplemented("unimplemented"))
        }
        async fn notify_app_ready(
            &self,
            _request: Request<()>,
        ) -> Result<Response<()>, tonic::Status> {
            Err(tonic::Status::unimplemented("unimplemented"))
        }
    }

    #[tokio::test]
    async fn test_create_channel_ip() {
        let listener =
            TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0)).await.unwrap();
        let server_addr = format!("http://0.0.0.0:{}", listener.local_addr().unwrap().port());

        let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();
        let server = tokio::spawn(async move {
            tonic::transport::Server::builder()
                .add_service(LauncherServer::new(TestLauncherServer {}))
                .serve_with_incoming_shutdown(
                    TcpListenerStream::new(listener),
                    shutdown_rx.map(|_| ()),
                )
                .await
        });
        let channel = create_channel(server_addr.try_into().unwrap()).await.unwrap();
        let mut client = LauncherClient::new(channel);
        assert_eq!(
            client.get_application_config(()).await.unwrap().into_inner().config,
            b"oak_application_config".to_vec()
        );
        let _ = shutdown_tx.send(());
        let _ = server.await;
    }

    #[cfg(feature = "vsock")]
    #[tokio::test]
    async fn test_create_channel_vsock() {
        // There is no VMADDR_PORT_ANY constant in  tokio_vsock crate. We pass
        // 0xFFFFFFFF instead.
        // Use VMADDR_CID_LOCAL as we do not know if this test will run in a VM or a
        // host.
        let listener = VsockListener::bind(VsockAddr::new(VMADDR_CID_LOCAL, 0xFFFFFFFF)).unwrap();

        // Construct the address manually.
        let server_addr = format!(
            "vsock://{}:{}",
            listener.local_addr().unwrap().cid(),
            listener.local_addr().unwrap().port()
        );
        let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();
        let server = tokio::spawn(async move {
            tonic::transport::Server::builder()
                .add_service(LauncherServer::new(TestLauncherServer {}))
                .serve_with_incoming_shutdown(listener.incoming(), shutdown_rx.map(|_| ()))
                .await
        });

        let channel = create_channel(server_addr.try_into().unwrap()).await.unwrap();
        let mut client = LauncherClient::new(channel);
        assert_eq!(
            client.get_application_config(()).await.unwrap().into_inner().config,
            b"oak_application_config".to_vec()
        );
        let _ = shutdown_tx.send(());
        let _ = server.await;
    }

    #[test]
    fn test_get_sock_addr_error() {
        match get_vsock_addr("vsock://:2".try_into().unwrap()) {
            Ok(_) => panic!("get_vsock_addr() should fail."),
            Err(e) => assert_eq!(e.to_string(), "invalid vsock CID"),
        }

        match get_vsock_addr("vsock://2:XX".try_into().unwrap()) {
            Ok(_) => panic!("get_vsock_addr() should fail."),
            Err(e) => assert_eq!(e.to_string(), "invalid vsock port"),
        }

        match get_vsock_addr("vsock://2".try_into().unwrap()) {
            Ok(_) => panic!("get_vsock_addr() should fail."),
            Err(e) => assert_eq!(e.to_string(), "malformed vsock address"),
        }
    }
}
