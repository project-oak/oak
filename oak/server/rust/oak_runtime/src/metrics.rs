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

use log::{error, info};
use prometheus::{Encoder, TextEncoder};
use std::{convert::Infallible, net::SocketAddr};

async fn process_metrics(_req: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder
        .encode(&metric_families, &mut buffer)
        .expect("Could not encode metrics data!");
    info!("Metrics size: {}", buffer.len());
    let response = Response::builder()
        .status(200)
        .header(CONTENT_TYPE, encoder.format_type())
        .body(Body::from(buffer))
        .expect("Error when building the HTTP response.");

    Ok(response)
}

pub async fn serve_metrics(port: u16) -> Result<(), Box<dyn std::error::Error>> {
    let addr = SocketAddr::from(([127, 0, 0, 1], port));

    // A `Service` is needed for every connection, so this
    // creates one from the `process_metrics` function.
    let make_svc = make_service_fn(|_conn| async {
        // service_fn converts our function into a `Service`
        Ok::<_, Infallible>(service_fn(process_metrics))
    });

    let server = Server::bind(&addr).serve(make_svc);

    info!("Started metrics server on port {}", port);

    // Run this server for... forever!
    if let Err(e) = server.await {
        error!("server error: {}", e);
    }
    Ok(())
}
