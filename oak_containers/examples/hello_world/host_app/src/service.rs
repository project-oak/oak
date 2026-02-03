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

use std::{pin::Pin, sync::Arc};

use anyhow::{Context, anyhow};
use futures::{Stream, StreamExt, channel::mpsc};
use oak_hello_world_proto::oak::containers::example::{
    enclave_application_client::EnclaveApplicationClient,
    host_application_server::{HostApplication, HostApplicationServer},
};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use tokio::{net::TcpListener, sync::Mutex, time::Duration};
use tokio_stream::wrappers::TcpListenerStream;
use tonic::transport::{Endpoint, channel::Channel};

/// The sample application's implementation of Oak's streaming service protocol.
struct HostApplicationImpl {
    enclave_app: Arc<Mutex<EnclaveApplicationClient<Channel>>>,
}

impl HostApplicationImpl {
    pub fn new(enclave_app: EnclaveApplicationClient<Channel>) -> Self {
        Self { enclave_app: Arc::new(Mutex::new(enclave_app)) }
    }
}

#[tonic::async_trait]
impl HostApplication for HostApplicationImpl {
    type OakSessionStream =
        Pin<Box<dyn Stream<Item = Result<SessionResponse, tonic::Status>> + Send + 'static>>;

    async fn oak_session(
        &self,
        request_stream: tonic::Request<tonic::Streaming<SessionRequest>>,
    ) -> Result<tonic::Response<Self::OakSessionStream>, tonic::Status> {
        // Clone the app implementation `Arc` so that we have a reference to use the in
        // callback below.
        let enclave_app = self.enclave_app.clone();

        let mut request_stream = request_stream.into_inner();
        let (mut tx, rx) = mpsc::channel(10);
        let mut enclave_app_stream = enclave_app.lock().await.oak_session(rx).await?.into_inner();

        let response_stream = async_stream::try_stream! {
            while let Some(req) = request_stream.next().await {
                let req = req.map_err(|err| tonic::Status::internal(format!("incoming request error: {err:?}")))?;
                println!("Host forwarding request {req:?}");
                tx.try_send(req).map_err(|err| tonic::Status::internal(format!("sending request failed: {err:?}")))?;
                let resp = enclave_app_stream.next().await.expect("should get response").map_err(|err| tonic::Status::internal(format!("upstream response error: {err:?}")))?;
                println!("Host forwarding response {resp:?}");
                yield resp
            }
        };

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::OakSessionStream))
    }
}

pub async fn create(
    listener: TcpListener,
    launcher_args: oak_containers_launcher::Args,
) -> anyhow::Result<()> {
    let mut launcher = oak_containers_launcher::Launcher::create(launcher_args)
        .await
        .map_err(|error| anyhow!("Failed to crate launcher: {error:?}"))?;
    let enclave_app_address = launcher
        .get_trusted_app_address()
        .await
        .map_err(|error| anyhow!("Failed to get app address: {error:?}"))?;
    let channel = Endpoint::from_shared(format!("http://{enclave_app_address}"))
        .context("couldn't form channel")?
        .connect_timeout(Duration::from_secs(120))
        .connect()
        .await
        .context("couldn't connect to enclave app")?;
    let app_client = EnclaveApplicationClient::new(channel);
    tonic::transport::Server::builder()
        .add_service(HostApplicationServer::new(HostApplicationImpl::new(app_client)))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
