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
    server::{apply_policy, WasmHandler},
    OakFunctionsBoxedExtensionFactory,
};
use anyhow::Context;
use log::Level;
use oak_functions_abi::proto::{ConfigurationInfo, Request, ServerPolicy};
use oak_logger::OakLogger;
use oak_utils::LogError;
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
    let function = move || wasm_handler.clone().handle_invoke(request);
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
    extensions: Vec<OakFunctionsBoxedExtensionFactory>,
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

    let grpc_unary_attestation_service =
        grpc_unary_attestation::proto::unary_session_server::UnarySessionServer::new(
            grpc_unary_attestation::server::AttestationServer::create(
                tee_certificate,
                request_handler,
                additional_info,
                ErrorLogger { logger },
            )
            .context("Couldn't create remote attestation server")?,
        );

    // Create a server and add the relevant service defintions. Server creation
    // and start is handled entirely witin each respective conditional arm, as
    // the added service alters the type signature of the created server.
    if cfg!(feature = "oak-web") {
        #[cfg(feature = "oak-web")]
        tonic::transport::Server::builder()
            .accept_http1(true)
            .add_service(tonic_web::enable(grpc_unary_attestation_service))
            .serve_with_shutdown(*address, terminate)
            .await
            .context("Couldn't start server")?;
    } else {
        tonic::transport::Server::builder()
            .add_service(grpc_unary_attestation_service)
            .serve_with_shutdown(*address, terminate)
            .await
            .context("Couldn't start server")?;
    };

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
