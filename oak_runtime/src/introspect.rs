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

use crate::{proto::oak::introspection_events::Events, Runtime};
use hyper::{
    header::{ACCESS_CONTROL_ALLOW_ORIGIN, CONTENT_TYPE},
    service::{make_service_fn, service_fn},
    Body, Error, Method, Request, Response, Server, StatusCode,
};
use log::info;
use prost::Message;
use regex::Regex;
use std::{net::SocketAddr, sync::Arc};

/// Wrap a string holding a Graphviz Dot graph description in an HTML template
/// suitable for live display.
// TODO(#672): Shift to a templating library.
fn dot_wrap(title: &str, graph: &str) -> String {
    format!(
        r###"
<!DOCTYPE html>
<meta charset="utf-8">
<title>{}</title>
<body>
<script src="https://d3js.org/d3.v5.min.js"
        integrity="sha384-M06Cb6r/Yrkprjr7ngOrJlzgekrkkdmGZDES/SUnkUpUol0/qjsaQWQfLzq0mcfg"
        crossorigin="anonymous"></script>
<script src="https://unpkg.com/@hpcc-js/wasm@0.3.6/dist/index.min.js"
        integrity="sha384-y8QckRXESCyo6DMRfBy8RKSRf6q/D6U6D8XUbUU5poU9144yTw98vyhHVjky6jCY"
        crossorigin="anonymous"></script>
<script src="https://unpkg.com/d3-graphviz@3.0.0/build/d3-graphviz.js"
        integrity="sha384-rhFJRiWvj+zkVQouZi5hc+vHuqhp1N8AnncxPSaKQ+PUhODpXC3Pgy4EcxjYCIYA"
        crossorigin="anonymous"></script>
<div id="graph" style="text-align: center;"></div>
<style>html, body, #graph, #graph > * {{ width: 100%; height: 100%; margin: 0;}}</style>
<script>d3.select("#graph").graphviz().renderDot(`
{}
`);</script>
"###,
        title, graph,
    )
}

/// Wrap a body of text in an HTML template suitable for display.
fn html_wrap(title: &str, body: &str) -> String {
    format!(
        r###"
<!DOCTYPE html>
<meta charset="utf-8">
<title>{}</title>
<body>
{}
"###,
        title, body
    )
}

// Look for a path like "/{kind}/{id}" and return the id value.
fn find_id(path: &str, kind: &str) -> Option<u64> {
    Regex::new(&format!(r"^/{}/(?P<id>\d+)/?$", kind))
        .unwrap()
        .captures(path)?
        .name("id")
        .unwrap()
        .as_str()
        .parse::<u64>()
        .ok()
}

// Look for a path like "/{kind}/{id}/{subid}" and return the id values.
fn find_ids(path: &str, kind: &str) -> Option<(u64, u64)> {
    let captures = Regex::new(&format!(r"^/{}/(?P<id>\d+)/(?P<subid>\d+)/?$", kind))
        .unwrap()
        .captures(path)?;
    let id = captures.name("id").unwrap().as_str().parse::<u64>().ok()?;
    let subid = captures
        .name("subid")
        .unwrap()
        .as_str()
        .parse::<u64>()
        .ok()?;
    Some((id, subid))
}

#[cfg(not(feature = "oak_introspection_client"))]
fn find_client_file(_path: &str) -> Option<(Vec<u8>, String)> {
    None
}

// Looks for a matching file used by the browser client and returns it
#[cfg(feature = "oak_introspection_client")]
fn find_client_file(path: &str) -> Option<(Vec<u8>, String)> {
    let filepath = Regex::new(r"^/dynamic/(?P<filepath>[^\s]+)$")
        .unwrap()
        .captures(path)?
        .name("filepath")
        .unwrap()
        .as_str();

    match filepath {
        "index.html" => Some((
            include_bytes!("../introspection_browser_client/dist/index.html").to_vec(),
            "text/html".to_string(),
        )),
        "index.js" => Some((
            include_bytes!("../introspection_browser_client/dist/index.js").to_vec(),
            "application/javascript".to_string(),
        )),
        _ => None,
    }
}

// Handler for a single HTTP request to the introspection server.
fn handle_request(
    req: Request<Body>,
    runtime: Arc<Runtime>,
) -> Result<Response<Body>, hyper::Error> {
    if req.method() != Method::GET {
        let mut method_not_allowed = Response::default();
        *method_not_allowed.status_mut() = StatusCode::METHOD_NOT_ALLOWED;
        return Ok(method_not_allowed);
    }
    // TODO(#672): Shift to a framework.
    let path = req.uri().path();
    if path == "/" {
        return Ok(Response::new(Body::from(html_wrap(
            "Data Structures",
            &runtime.html(),
        ))));
    } else if path == "/graph" {
        return Ok(Response::new(Body::from(dot_wrap(
            "Runtime Graph",
            &runtime.graph(),
        ))));
    } else if path == "/objcount" {
        return Ok(Response::new(Body::from(html_wrap(
            "Object Counts",
            &runtime.html_counts(),
        ))));
    // Endpoint to load the list introspection events, serialized via protobuf
    } else if path == "/introspection-events" {
        let events_message = Events {
            events: Vec::from(runtime.introspection_event_queue.lock().unwrap().clone()),
        };

        let mut buffer: Vec<u8> = Vec::new();
        events_message.encode(&mut buffer).unwrap();

        let mut response = Response::new(Body::from(buffer));

        response
            .headers_mut()
            // Allow browsers from any origin (such as the introspection client
            // dev server) to access this resource. https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Access-Control-Allow-Origin
            .insert(ACCESS_CONTROL_ALLOW_ORIGIN, "*".parse().unwrap());
        response.headers_mut().insert(
            CONTENT_TYPE,
            // There isn't a standardized content-type for protobuf messages
            // yet. We use the non-standard type used by Google's python API
            // client: https://github.com/googleapis/google-api-python-client/blob/master/googleapiclient/model.py
            "application/x-protobuf".parse().unwrap(),
        );

        return Ok(response);
    } else if let Some((file, content_type)) = find_client_file(path) {
        let mut response = Response::new(Body::from(file));
        response
            .headers_mut()
            .insert(CONTENT_TYPE, content_type.parse().unwrap());

        return Ok(response);
    } else if let Some(node_id) = find_id(path, "node") {
        if let Some(body) = runtime.html_for_node(node_id) {
            return Ok(Response::new(Body::from(html_wrap(
                &format!("Node {}", node_id),
                &body,
            ))));
        }
    } else if let Some((node_id, handle)) = find_ids(path, "node") {
        if let Some(body) = runtime.html_for_handle(node_id, handle) {
            return Ok(Response::new(Body::from(html_wrap(
                &format!("Node {} Handle {}", node_id, handle),
                &body,
            ))));
        }
    }
    let mut not_found = Response::default();
    *not_found.status_mut() = StatusCode::NOT_FOUND;
    Ok(not_found)
}

async fn make_server(
    port: u16,
    runtime: Arc<Runtime>,
    termination_notificiation_receiver: tokio::sync::oneshot::Receiver<()>,
) {
    // Initialize SocketAddr to listen on.
    let addr = SocketAddr::from((std::net::Ipv6Addr::UNSPECIFIED, port));
    info!("starting introspection server on {:?}", addr);

    // Initialize MakeService to handle each connection.
    let make_service = make_service_fn(move |_| {
        // The `Arc<Runtime>` is moved into this closure, but it needs to be
        // cloned because this closure is called for every connection.
        let runtime = runtime.clone();

        async move {
            Ok::<_, Error>(service_fn(move |req| {
                let runtime = runtime.clone();
                async move { handle_request(req, runtime) }
            }))
        }
    });

    // Bind an address and serve incoming connections.
    let server = Server::bind(&addr).serve(make_service);
    let graceful = server.with_graceful_shutdown(async {
        // Treat notification failure the same as a notification.
        let _ = termination_notificiation_receiver.await;
    });

    // Run until asked to terminate.
    let result = graceful.await;
    info!("introspection server terminated with {:?}", result);
}

// Start running an introspection server on the given port, running until the
// `termination_notificiation_receiver` is triggered.
pub fn serve(
    port: u16,
    runtime: Arc<Runtime>,
    termination_notificiation_receiver: tokio::sync::oneshot::Receiver<()>,
) {
    let mut tokio_runtime = tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
    tokio_runtime.block_on(make_server(
        port,
        runtime,
        termination_notificiation_receiver,
    ));
}
