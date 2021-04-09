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

use anyhow::Context;
use http::{request::Request, response::Response};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Server, StatusCode,
};
use log::info;
use std::sync::Arc;

const MAIN_FUNCTION_NAME: &str = "main";

// An ephemeral request handler with a Wasm module for handling the requests.
#[derive(Clone)]
pub(crate) struct WasmHandler {
    // Wasm module to be served on each invocation. `Arc` is needed to make `WasmHandler`
    // cloneable.
    module: Arc<wasmi::Module>,
}

/// Encapsulates the state of a Wasm invocation for a single user request.
struct WasmState {
    instance: wasmi::ModuleRef,
    #[allow(dead_code)]
    memory: wasmi::MemoryRef,
    #[allow(dead_code)]
    request_bytes: Vec<u8>,
    response_bytes: Vec<u8>,
}

impl WasmState {
    fn new(module: &wasmi::Module, request_bytes: Vec<u8>) -> anyhow::Result<WasmState> {
        // TODO(#1919): Make request body available to the Wasm module via ABI functions.
        // TODO(#1919): Get the actual response from the Wasm module via ABI functions.
        let instance = wasmi::ModuleInstance::new(module, &wasmi::ImportsBuilder::default())
            .context("failed to instantiate Wasm module")?
            .assert_no_start();
        let memory = instance
            .export_by_name("memory")
            .context("could not find Wasm `memory` export")?
            .as_memory()
            .cloned()
            .context("could not interpret Wasm `memory` export as memory")?;
        Ok(WasmState {
            instance,
            memory,
            request_bytes,
            response_bytes: "Welcome to Oak Functions\n".as_bytes().to_vec(),
        })
    }

    fn invoke(&mut self) {
        let result = self
            .instance
            .invoke_export(MAIN_FUNCTION_NAME, &[], &mut wasmi::NopExternals);
        info!(
            "{:?}: Running Wasm module completed with result: {:?}",
            std::thread::current().id(),
            result
        );
    }
}

impl WasmHandler {
    pub(crate) fn create(wasm_module_bytes: &[u8]) -> anyhow::Result<Self> {
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)?;
        Ok(WasmHandler {
            module: Arc::new(module),
        })
    }

    pub(crate) async fn handle_request(
        &self,
        req: Request<Body>,
    ) -> anyhow::Result<Response<Body>> {
        info!("The request is: {:?}", req);
        match (req.method(), req.uri().path()) {
            (&hyper::Method::POST, "/invoke") => self.handle_invoke(req).await,
            (method, path) => http::response::Builder::new()
                .status(StatusCode::BAD_REQUEST)
                .body(format!("Invalid request: {} {}\n", method, path).into())
                .context("Couldn't create response"),
        }
    }

    async fn handle_invoke(&self, req: Request<Body>) -> anyhow::Result<Response<Body>> {
        let request_bytes = hyper::body::to_bytes(req.into_body()).await.unwrap();
        let mut wasm_state = WasmState::new(&self.module, request_bytes.to_vec())?;
        wasm_state.invoke();
        http::response::Builder::new()
            .status(StatusCode::OK)
            .body(Body::from(wasm_state.response_bytes))
            .context("Couldn't create response")
    }
}

/// Starts an HTTP server on the given address, serving the main function of the given Wasm module.
pub async fn create_and_start_server(
    address: &str,
    wasm_module_bytes: &[u8],
    notify_receiver: tokio::sync::oneshot::Receiver<()>,
) -> anyhow::Result<()> {
    let wasm_handler = WasmHandler::create(wasm_module_bytes)?;

    // A `Service` is needed for every connection. Here we create a service using
    // the`wasm_handler`.
    let service = make_service_fn(move |_conn| {
        let wasm_handler = wasm_handler.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let wasm_handler = wasm_handler.clone();
                async move { wasm_handler.handle_request(req).await }
            }))
        }
    });

    let server = Server::bind(&address.parse()?).serve(service);

    let graceful_server = server.with_graceful_shutdown(async {
        // Treat notification failure the same as a notification.
        let _ = notify_receiver.await;
    });

    info!(
        "{:?}: Started HTTP server on {:?}",
        std::thread::current().id(),
        &address
    );

    // Run until asked to terminate...
    let result = graceful_server.await;
    info!(
        "HTTP server on addr {} terminated with {:?}",
        &address, result
    );
    Ok(())
}
