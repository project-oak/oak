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
    lookup::LookupData,
    proto::grpc_handler_server::{GrpcHandler, GrpcHandlerServer},
    server::{apply_policy, Policy, WasmHandler},
};
use anyhow::Context;
use log::Level;
use oak_functions_abi::proto::{Request, Response};
use std::{convert::TryInto, future::Future, net::SocketAddr, sync::Arc};

/// A gRPC server with an `invoke` method to handle incoming requests to an Oak Functions
/// application.
pub struct FunctionsServer {
    wasm_handler: WasmHandler,
    policy: Policy,
}

#[tonic::async_trait]
impl GrpcHandler for FunctionsServer {
    async fn invoke(
        &self,
        request: tonic::Request<Request>,
    ) -> Result<tonic::Response<Response>, tonic::Status> {
        let policy = self.policy;
        let wasm_handler = self.wasm_handler.clone();
        let function = move || handle_request(wasm_handler, request);
        let policy = policy.try_into().map_err(|err| {
            tonic::Status::new(tonic::Code::Internal, format!("invalid policy: {:?}", err))
        })?;
        let response = apply_policy(policy, function).await.map_err(|err| {
            tonic::Status::new(tonic::Code::Internal, format!("internal error: {:?}", err))
        })?;
        Ok(tonic::Response::new(response))
    }
}

pub async fn handle_request(
    wasm_handler: WasmHandler,
    request: tonic::Request<Request>,
) -> anyhow::Result<Response> {
    let bytes = request.into_inner().body;
    wasm_handler.handle_invoke(bytes).await
}

/// Starts a gRPC server on the given address, serving the `main` function of the given Wasm module.
pub async fn create_and_start_grpc_server<F: Future<Output = ()>>(
    address: &SocketAddr,
    wasm_module_bytes: &[u8],
    lookup_data: Arc<LookupData>,
    policy: Policy,
    terminate: F,
    logger: Logger,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes, lookup_data, logger.clone())?;

    logger.log_public(
        Level::Info,
        &format!(
            "{:?}: Starting gRPC server on {:?}",
            std::thread::current().id(),
            &address
        ),
    );

    // A `Service` is needed for every connection. Here we create a service using the
    // `wasm_handler`.
    tonic::transport::Server::builder()
        .add_service(GrpcHandlerServer::new(FunctionsServer {
            wasm_handler,
            policy,
        }))
        .serve_with_shutdown(*address, terminate)
        .await
        .context("Couldn't start server")?;

    Ok(())
}
