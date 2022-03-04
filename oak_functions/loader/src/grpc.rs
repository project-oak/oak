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
//

//! gRPC server for Oak Functions.

use crate::{
    logger::Logger,
    server::{apply_policy, BoxedExtensionFactory, WasmHandler},
};
use anyhow::Context;
use grpc_streaming_attestation::{
    proto::streaming_session_server::StreamingSessionServer,
    server::{AttestationServer, LogError},
};
use log::Level;
use oak_functions_abi::proto::{ConfigurationInfo, Request, ServerPolicy};
use oak_logger::OakLogger;
use prost::Message;
use std::{future::Future, net::SocketAddr};

async fn handle_request(
    wasm_handler: WasmHandler,
    policy: ServerPolicy,
    decrypted_request: Vec<u8>,
) -> anyhow::Result<Vec<u8>> {
    let request = Request {
        body: decrypted_request,
    };
    let function = async move || wasm_handler.clone().handle_invoke(request).await;
    let policy = policy.clone();
    let response = apply_policy(policy, function)
        .await
        .context("internal error")?;
    Ok(response.encode_to_vec())
}

/// Creates a [`WasmHandler`] with the given Wasm module, lookup data, metrics aggregator, and
/// extensions.
pub fn create_wasm_handler(
    wasm_module_bytes: &[u8],
    extensions: Vec<BoxedExtensionFactory>,
    logger: Logger,
) -> anyhow::Result<WasmHandler> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, extensions, logger)?;

    Ok(wasm_handler)
}

/// Starts a gRPC server on the given address, serving the `main` function from the given
/// [`WasmHandler`].
#[allow(clippy::too_many_arguments)]
pub async fn create_and_start_grpc_server<F: Future<Output = ()>>(
    address: &SocketAddr,
    wasm_handler: WasmHandler,
    tee_certificate: Vec<u8>,
    policy: ServerPolicy,
    config_info: ConfigurationInfo,
    terminate: F,
    logger: Logger,
) -> anyhow::Result<()> {
    logger.log_public(
        Level::Info,
        &format!(
            "{:?}: Starting gRPC server on {:?}",
            std::thread::current().id(),
            &address
        ),
    );

    let request_handler =
        async move |request| handle_request(wasm_handler, policy.clone(), request).await;

    let additional_info = config_info.encode_to_vec();
    // A `Service` is needed for every connection. Here we create a service using the
    // `wasm_handler`.
    tonic::transport::Server::builder()
        .add_service(StreamingSessionServer::new(
            AttestationServer::create(
                tee_certificate,
                request_handler,
                additional_info,
                ErrorLogger { logger },
            )
            .context("Couldn't create remote attestation server")?,
        ))
        .serve_with_shutdown(*address, terminate)
        .await
        .context("Couldn't start server")?;

    Ok(())
}

#[derive(Clone)]
struct ErrorLogger {
    logger: Logger,
}

impl LogError for ErrorLogger {
    fn log_error(&self, error: &str) {
        self.logger.log_public(
            Level::Warn,
            &format!(
                "{:?}: Remote attestation error: {}",
                std::thread::current().id(),
                error
            ),
        );
    }
}
