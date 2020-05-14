//
// Copyright 2020 The Project Oak Authors
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

use hyper::{
    header::CONTENT_TYPE,
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use log::info;
use prometheus::{Encoder, TextEncoder};
use std::{net::SocketAddr, sync::Arc};

use crate::runtime::Runtime;

#[derive(Debug)]
enum MetricsServerError {
    EncodingError(String),
    ResponseError(String),
}

impl std::fmt::Display for MetricsServerError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            MetricsServerError::EncodingError(msg) => write!(f, "Metrics server error: {}", msg),
            MetricsServerError::ResponseError(msg) => write!(f, "Metrics server error: {}", msg),
        }
    }
}

impl std::error::Error for MetricsServerError {}

async fn serve_metrics(_req: Request<Body>) -> Result<Response<Body>, MetricsServerError> {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder.encode(&metric_families, &mut buffer).map_err(|e| {
        MetricsServerError::EncodingError(format!("Could not encode metrics data: {}", e))
    })?;

    info!("Metrics size: {}", buffer.len());

    Response::builder()
        .status(http::StatusCode::OK)
        .header(CONTENT_TYPE, encoder.format_type())
        .body(Body::from(buffer))
        .map_err(|e| {
            MetricsServerError::ResponseError(format!("Could not build the response: {}", e))
        })
}

async fn make_server(port: u16, notify_receiver: tokio::sync::oneshot::Receiver<()>) {
    let addr = SocketAddr::from(([0, 0, 0, 0], port));

    // A `Service` is needed for every connection, so this
    // creates one from the `process_metrics` function.
    let make_svc = make_service_fn(|_conn| async {
        // service_fn converts our function into a `Service`
        Ok::<_, hyper::Error>(service_fn(serve_metrics))
    });

    let server = Server::bind(&addr).serve(make_svc);
    let graceful = server.with_graceful_shutdown(async {
        // Treat notification failure the same as a notification.
        let _ = notify_receiver.await;
    });
    info!(
        "{:?}: Started metrics server on port {:?}",
        std::thread::current().id(),
        port
    );

    // Run until asked to terminate...
    let result = graceful.await;
    info!("metrics server terminated with {:?}", result);
}

// Start running a metrics server on the given port, running until the `notify_receiver` is
// triggered.
pub fn start_metrics_server(
    port: u16,
    _runtime: Arc<Runtime>,
    notify_receiver: tokio::sync::oneshot::Receiver<()>,
) {
    let mut tokio_runtime = tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
    tokio_runtime.block_on(make_server(port, notify_receiver));
}
