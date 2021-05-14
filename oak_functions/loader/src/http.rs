//
// Copyright 2021 The Project Oak Authors
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

//! HTTP/2 server for Oak Functions.

use crate::{
    logger::Logger,
    lookup::LookupData,
    server::{apply_policy, Policy, WasmHandler},
};
use anyhow::Context;
use http::request::Request;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server,
};
use log::Level;
use oak_functions_abi::proto::{Response, StatusCode};
use prost::Message;
use std::{convert::TryInto, future::Future, net::SocketAddr, sync::Arc};

/// Creates an HTTP response, with status `OK`, and the protobuf-encoded `response` as its body.
pub fn create_http_response(response: Response) -> anyhow::Result<http::response::Response<Body>> {
    let mut encoded = vec![];
    response
        .encode(&mut encoded)
        .context("unreachable: buffer is too small for the encoded message")?;
    http::response::Builder::new()
        .status(hyper::StatusCode::OK)
        .body(Body::from(encoded))
        .context("unreachable: couldn't create response")
}

/// Starts an HTTP server on the given address, serving the `main` function of the given Wasm
/// module.
pub async fn create_and_start_http_server<F: Future<Output = ()>>(
    address: &SocketAddr,
    wasm_module_bytes: &[u8],
    lookup_data: Arc<LookupData>,
    policy: Policy,
    terminate: F,
    logger: Logger,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, lookup_data, logger.clone())?;
    let logger_clone = logger.clone();

    // A `Service` is needed for every connection. Here we create a service using the
    // `wasm_handler`.
    let service = make_service_fn(move |_conn| {
        let wasm_handler = wasm_handler.clone();
        let logger = logger_clone.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let wasm_handler = wasm_handler.clone();
                let logger = logger.clone();
                let func = move || handle_request(wasm_handler, req, logger);
                async move {
                    let response = apply_policy(policy.try_into()?, func).await?;
                    create_http_response(response)
                }
            }))
        }
    });

    let server = Server::bind(address)
        .http2_only(true)
        .serve(service)
        .with_graceful_shutdown(terminate);

    logger.log_public(
        Level::Info,
        &format!(
            "{:?}: Started HTTP server on {:?}",
            std::thread::current().id(),
            &address
        ),
    );

    // Run until asked to terminate...
    let result = server.await;

    logger.log_public(
        Level::Info,
        &format!(
            "HTTP server on addr {} terminated with {:?}",
            &address, result
        ),
    );
    Ok(())
}

pub async fn handle_request(
    wasm_handler: WasmHandler,
    req: Request<Body>,
    logger: Logger,
) -> anyhow::Result<Response> {
    logger.log_sensitive(Level::Info, &format!("The request is: {:?}", req));
    match (req.method(), req.uri().path()) {
        (&hyper::Method::POST, "/invoke") => {
            let request_bytes = hyper::body::to_bytes(req.into_body())
                .await
                .unwrap()
                .to_vec();
            wasm_handler.handle_invoke(request_bytes).await
        }
        (method, path) => Ok(Response::create(
            StatusCode::BadRequest,
            format!("Invalid request: {} {}\n", method, path)
                .as_bytes()
                .to_vec(),
        )),
    }
}
