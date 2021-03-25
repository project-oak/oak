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
use std::{fs, net::SocketAddr, sync::Arc};

const MAIN_FUNCTION_NAME: &str = "main";

pub struct WasmServer {
    /// Server address to listen client requests on.
    address: SocketAddr,
    /// Request handler that runs the wasm_module.
    wasm_engine: WasmEngine,
}

#[derive(Clone)]
struct WasmEngine {
    // wasm module to be served on each invocation.
    module: Arc<wasmi::Module>,
}

impl WasmEngine {
    async fn handle_request(&self, req: Request<Body>) -> anyhow::Result<Response<Body>> {
        // TODO(#1919): Make request available to the wasm module via ABI functions.
        info!("The request is: {:?}", req);

        let instance = wasmi::ModuleInstance::new(&self.module, &wasmi::ImportsBuilder::default())
            .expect("failed to instantiate wasm module")
            .assert_no_start();

        let result = instance.invoke_export(MAIN_FUNCTION_NAME, &[], &mut wasmi::NopExternals);

        info!(
            "{:?}: Running wasm module completed with result: {:?}",
            std::thread::current().id(),
            result
        );

        // TODO(#1919): Get the actual response from the wasm module via ABI functions.
        http::response::Builder::new()
            .status(StatusCode::BAD_REQUEST)
            .body(Body::from("Not implemented yet.\n"))
            .context("Couldn't create response")
    }
}

impl WasmServer {
    pub fn create(address: &str, wasm_path: &str) -> anyhow::Result<Self> {
        let wasm_module_bytes =
            fs::read(&wasm_path).with_context(|| format!("Couldn't read file {}", wasm_path))?;
        let module = wasmi::Module::from_buffer(&wasm_module_bytes)?;
        Ok(WasmServer {
            address: address.parse()?,
            wasm_engine: WasmEngine {
                module: Arc::new(module),
            },
        })
    }
    pub async fn start(
        &self,
        notify_receiver: tokio::sync::oneshot::Receiver<()>,
    ) -> anyhow::Result<()> {
        // A `Service` is needed for every connection. Here we create a service using the `handler`.
        let service = make_service_fn(move |_conn| {
            let wasm_engine = self.wasm_engine.clone();
            async move {
                Ok::<_, hyper::Error>(service_fn(move |req| {
                    let wasm_engine = wasm_engine.clone();
                    async move { wasm_engine.handle_request(req).await }
                }))
            }
        });

        let server = Server::bind(&self.address).serve(service);

        let graceful_server = server.with_graceful_shutdown(async {
            // Treat notification failure the same as a notification.
            let _ = notify_receiver.await;
        });

        info!(
            "{:?}: Started HTTP server on {:?}",
            std::thread::current().id(),
            &self.address
        );

        // Run until asked to terminate...
        let result = graceful_server.await;
        info!(
            "HTTP server on addr {:?} terminated with {:?}",
            self.address, result
        );
        Ok(())
    }
}
