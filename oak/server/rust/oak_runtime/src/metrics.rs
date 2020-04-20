use hyper::{
    header::CONTENT_TYPE,
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};

use log::info;
use prometheus::{
    labels, opts, register_counter, register_gauge, register_histogram_vec, Counter, Encoder,
    Gauge, HistogramVec, TextEncoder,
};
use std::{convert::Infallible, net::SocketAddr};

lazy_static::lazy_static! {
pub static ref HTTP_COUNTER: Counter = register_counter!(opts!(
    "http_requests_total",
    "Total number of HTTP requests made.",
    labels! {"handler" => "all",}
))
.unwrap();
pub static ref HTTP_BODY_GAUGE: Gauge = register_gauge!(opts!(
    "http_response_size_bytes",
    "The HTTP response sizes in bytes.",
    labels! {"handler" => "all",}
))
.unwrap();
pub static ref HTTP_REQ_HISTOGRAM: HistogramVec = register_histogram_vec!(
    "http_request_duration_seconds",
    "The HTTP request latencies in seconds.",
    &["handler"]
)
.unwrap();
pub static ref NUM_NODES: Gauge = register_gauge!(opts!(
    "num_nodes",
    "Number of nodes in the runtime.",
    labels! {"handler" => "all",}
))
.unwrap();
}

async fn process_metrics(_req: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder.encode(&metric_families, &mut buffer).unwrap();
    info!("Metrics size: {}", buffer.len());
    let response = Response::builder()
        .status(200)
        .header(CONTENT_TYPE, encoder.format_type())
        .body(Body::from(buffer))
        .unwrap();

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
        eprintln!("server error: {}", e);
    }
    Ok(())
}
