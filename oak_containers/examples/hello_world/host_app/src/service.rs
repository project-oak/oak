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

use std::{future::Future, pin::Pin, sync::Arc};

use anyhow::{anyhow, Context};
use futures::{channel::mpsc, Stream, StreamExt};
use oak_hello_world_proto::oak::containers::example::{
    enclave_application_client::EnclaveApplicationClient,
    host_application_server::{HostApplication, HostApplicationServer},
};
use oak_proto_rust::oak::session::v1::{RequestWrapper, ResponseWrapper};
use tokio::{net::TcpListener, sync::Mutex, time::Duration};
use tokio_stream::wrappers::TcpListenerStream;
use tonic::transport::{channel::Channel, Endpoint};

/// The sample application's implementation of Oak's streaming service protocol.
struct HostApplicationImpl {
    enclave_app: Arc<Mutex<EnclaveApplicationClient<Channel>>>,
}

impl HostApplicationImpl {
    pub fn new(enclave_app: EnclaveApplicationClient<Channel>) -> Self {
        Self { enclave_app: Arc::new(Mutex::new(enclave_app)) }
    }
}

#[derive(Debug)]
enum Action {
    Receive(Option<Result<RequestWrapper, tonic::Status>>),
    Send(Option<Result<ResponseWrapper, tonic::Status>>),
}

async fn forward_stream<Fut>(
    request_stream: tonic::Streaming<RequestWrapper>,
    upstream_starter: impl FnOnce(mpsc::Receiver<RequestWrapper>) -> Fut,
) -> Result<impl Stream<Item = Result<ResponseWrapper, tonic::Status>>, tonic::Status>
where
    Fut: Future<Output = Result<tonic::Response<tonic::Streaming<ResponseWrapper>>, tonic::Status>>,
{
    let mut request_stream = request_stream;
    let (mut tx, rx) = mpsc::channel(10);

    let mut upstream = upstream_starter(rx).await?.into_inner();

    Ok(async_stream::try_stream! {
        loop {
            // This block waits for either a request message or a resposne message,
            // so that it can forward the requests on to the TEE application, or
            // forward the respones back to the client.
            let action: Action = async {
                tokio::select! {
                    req = request_stream.next() => Action::Receive(req),
                    resp = upstream.next() => Action::Send(resp),
                }
            }.await;


            match action {
                Action::Receive(req) => match req {
                    None => break,
                    Some(req) => tx
                        .try_send(req.map_err(|err| tonic::Status::internal(format!("incoming request error: {err:?}")))?)
                        .map_err(|err| tonic::Status::internal(format!("sending request failed: {err:?}")))?,
                }
                Action::Send(resp) => match resp {
                    None => break,
                    Some(resp) => yield resp.map_err(|err| tonic::Status::internal(format!("upstream response error: {err:?}")))?
                }
            }
        }
    })
}

#[tonic::async_trait]
impl HostApplication for HostApplicationImpl {
    type SessionStream =
        Pin<Box<dyn Stream<Item = Result<ResponseWrapper, tonic::Status>> + Send + 'static>>;

    async fn session(
        &self,
        request: tonic::Request<tonic::Streaming<RequestWrapper>>,
    ) -> Result<tonic::Response<Self::SessionStream>, tonic::Status> {
        let request_stream = request.into_inner();

        let enclave_app = self.enclave_app.clone();

        let response_stream = forward_stream(request_stream, |rx| async move {
            let mut app = enclave_app.lock().await;
            app.legacy_session(rx).await.map_err(|err| {
                tonic::Status::internal(format!("Failed to start enclave app stream: {err:?}"))
            })
        })
        .await?;

        Ok(tonic::Response::new(Box::pin(response_stream) as Self::SessionStream))
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
