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
use oak_containers_launcher::Launcher;
use oak_proto_rust::oak::session::v1::{
    request_wrapper, response_wrapper, GetEndorsedEvidenceResponse, InvokeRequest, InvokeResponse,
    RequestWrapper, ResponseWrapper,
};
use prost::Message;
use tokio::{net::TcpListener, sync::Mutex};

use crate::app_client::TrustedApplicationClient;

async fn handle_request(
    request: RequestWrapper,
    launcher: Arc<Mutex<Launcher>>,
    trusted_app: Arc<Mutex<TrustedApplicationClient>>,
) -> anyhow::Result<ResponseWrapper> {
    let request = request.request.context("No request in wrapper")?;

    let response = match request {
        request_wrapper::Request::GetEndorsedEvidenceRequest(_) => {
            let endorsed_evidence = {
                launcher.lock().await.get_endorsed_evidence().await.map_err(|err| {
                    tonic::Status::internal(format!("launcher evidence get failed: {err:?}"))
                })?
            };
            response_wrapper::Response::GetEndorsedEvidenceResponse(GetEndorsedEvidenceResponse {
                endorsed_evidence: Some(endorsed_evidence),
            })
        }
        request_wrapper::Request::InvokeRequest(InvokeRequest { encrypted_request }) => {
            let encrypted_response = trusted_app
                .lock()
                .await
                .hello(encrypted_request.expect("empty encrypted request"))
                .await
                .map_err(|err| tonic::Status::internal(format!("hello failed: {err:?}")))?;
            response_wrapper::Response::InvokeResponse(InvokeResponse {
                encrypted_response: Some(encrypted_response),
            })
        }
    };
    Ok(ResponseWrapper { response: Some(response) })
}

/// Start a demo HTTP server that will conform to the demo HTTP protocol
pub async fn serve(
    listener: TcpListener,
    launcher_args: oak_containers_launcher::Args,
) -> Result<(), anyhow::Error> {
    let mut launcher = oak_containers_launcher::Launcher::create(launcher_args)
        .await
        .map_err(|error| anyhow!("Failed to crate launcher: {error:?}"))?;
    let trusted_app_address = launcher
        .get_trusted_app_address()
        .await
        .map_err(|error| anyhow!("Failed to get app address: {error:?}"))?;
    let app_client = TrustedApplicationClient::create(format!("http://{trusted_app_address}"))
        .await
        .map_err(|error| anyhow!("Failed to create trusted application client: {error:?}"))?;

    let launcher = Arc::new(Mutex::new(launcher));
    let app_client = Arc::new(Mutex::new(app_client));

    loop {
        let (tcp, _) = listener.accept().await?;

        let io = TokioIo::new(tcp);

        let launcher = Arc::clone(&launcher);
        let app_client = Arc::clone(&app_client);

        tokio::task::spawn(async move {
            if let Err(err) = http1::Builder::new()
                .timer(TokioTimer::new())
                .serve_connection(
                    io,
                    service_fn(|request: Request<body::Incoming>| {
                        // These need to be cloned before entering the async move block.
                        let launcher = Arc::clone(&launcher);
                        let app_client = Arc::clone(&app_client);
                        async move {
                            let serialized = request.collect().await?.to_bytes().to_vec();
                            let request_wrapper = RequestWrapper::decode(&serialized[..])?;
                            let response =
                                handle_request(request_wrapper, launcher, app_client).await?;
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
