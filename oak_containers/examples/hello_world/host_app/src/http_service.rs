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

#![deny(warnings)]

use std::sync::Arc;

use anyhow::{anyhow, Context};
use bytes::Bytes;
use http_body_util::{BodyExt, Full};
use hyper::{body, server::conn::http1, service::service_fn, Request, Response};
use hyper_util::rt::{TokioIo, TokioTimer};
use oak_proto_rust::oak::session::v1::{RequestWrapper, ResponseWrapper};
use prost::Message;
use tokio::{net::TcpListener, sync::Mutex};

use crate::app_client::EnclaveApplicationClient;

async fn handle_request(
    request: RequestWrapper,
    enclave_app: Arc<Mutex<EnclaveApplicationClient>>,
) -> tonic::Result<ResponseWrapper> {
    // This is not how we should actually use the streaming interface, but it
    // works for HPKE, as long as all requests go to the same machine.
    let mut response_stream =
        enclave_app.lock().await.legacy_session(tokio_stream::iter(vec![request])).await.map_err(
            |err| tonic::Status::internal(format!("starting streaming session failed: {err:?}")),
        )?;

    response_stream
        .message()
        .await?
        .context("no response wrapper was returned")
        .map_err(|err| tonic::Status::internal(format!("failed to get response {err:?}")))
}

/// Start a demo HTTP server that will conform to the demo HTTP protocol
pub async fn serve(
    listener: TcpListener,
    launcher_args: oak_containers_launcher::Args,
) -> Result<(), anyhow::Error> {
    let mut launcher = oak_containers_launcher::Launcher::create(launcher_args)
        .await
        .map_err(|error| anyhow!("Failed to crate launcher: {error:?}"))?;
    let enclave_app_address = launcher
        .get_trusted_app_address()
        .await
        .map_err(|error| anyhow!("Failed to get app address: {error:?}"))?;
    let app_client = EnclaveApplicationClient::create(format!("http://{enclave_app_address}"))
        .await
        .map_err(|error| anyhow!("Failed to create enclave application client: {error:?}"))?;

    let app_client = Arc::new(Mutex::new(app_client));

    loop {
        let (tcp, _) = listener.accept().await?;

        let io = TokioIo::new(tcp);

        let app_client = Arc::clone(&app_client);

        tokio::task::spawn(async move {
            if let Err(err) = http1::Builder::new()
                .timer(TokioTimer::new())
                .serve_connection(
                    io,
                    service_fn(|request: Request<body::Incoming>| {
                        // These need to be cloned before entering the async move block.
                        let app_client = Arc::clone(&app_client);
                        async move {
                            let serialized = request.collect().await?.to_bytes().to_vec();
                            let request_wrapper = RequestWrapper::decode(&serialized[..])?;
                            let response = handle_request(request_wrapper, app_client).await?;
                            let serialized = response.encode_to_vec();
                            Ok::<_, anyhow::Error>(Response::new(Full::new(Bytes::from(
                                serialized,
                            ))))
                        }
                    }),
                )
                .await
            {
                println!("Error serving connection: {:?}", err);
            }
        });
    }
}
