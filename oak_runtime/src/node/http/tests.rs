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

use super::*;
use maplit::hashmap;
use oak_abi::{label::Label, proto::oak::application::ApplicationConfiguration};
use std::{fs, option::Option, thread::JoinHandle};

static LOCAL_CA: &str = "../examples/certs/local/ca.pem";
static GCP_CA: &str = "../examples/certs/gcp/ca.pem";

struct HttpServerTester {
    runtime: RuntimeProxy,
    server_node_thread_handle: Option<JoinHandle<()>>,
    oak_node_simulator_thread_handle: Option<JoinHandle<()>>,
    notify_sender: Option<tokio::sync::oneshot::Sender<()>>,
}

impl HttpServerTester {
    /// Create a new runtime and test server.
    /// port: The port on which the server is started
    /// number_of_requests: the number of requests the server expects to receive. This parameter is
    /// passed to `oak_node_simulator` to set up the Oak node that servers the requests.
    fn new(port: u32, number_of_requests: i32) -> HttpServerTester {
        let runtime = create_runtime();
        let server_node = create_server_node(port);
        let (init_receiver, invocation_receiver) = create_communication_channel(&runtime);

        // Start the server node
        let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();
        let runtime_proxy = runtime.clone();
        // TODO(#1186): Use tokio instead of spawning a thread.
        let server_node_thread = std::thread::spawn(move || {
            server_node.run(runtime_proxy, init_receiver, notify_receiver)
        });

        // Simulate an Oak node that responds with 200 (OK) to every request it receives
        // TODO(#1186): Use tokio instead of spawning a thread.
        let runtime_proxy = runtime.clone();
        let oak_node_simulator_thread = Some(std::thread::spawn(move || {
            oak_node_simulator(number_of_requests, &runtime_proxy, invocation_receiver);
        }));

        HttpServerTester {
            runtime,
            server_node_thread_handle: Some(server_node_thread),
            oak_node_simulator_thread_handle: oak_node_simulator_thread,
            notify_sender: Some(notify_sender),
        }
    }

    fn cleanup(&mut self) {
        if let Some(sender) = self.notify_sender.take() {
            sender.send(()).unwrap_or_else(|()| {
                debug!("Test node already dropped `notify_receiver`.");
            })
        }
        if let Some(handle) = self.server_node_thread_handle.take() {
            let _ = handle.join();
        };
        if let Some(handle) = self.oak_node_simulator_thread_handle.take() {
            let _ = handle.join();
        };

        // stop the runtime and any servers it is running
        self.runtime.runtime.stop();
    }
}

fn init_logger() {
    // Ignore the result. We don't want to panic if the logger cannot be initialized, or is being
    // initialized more than once. Also, if the logger is not initialized, we cannot log an
    // error!
    let _res = env_logger::builder().is_test(true).try_init();
}

#[tokio::test]
async fn test_https_server_can_serve_https_requests() {
    init_logger();

    // Start a runtime with an HTTP server node, and a thread simulating an Oak node to respond to
    // HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2525, 1);
    let client_with_valid_tls = create_client(LOCAL_CA);

    // Send an HTTPS request, and check that response has StatusCode::OK
    let resp = send_request(client_with_valid_tls, "https://localhost:2525").await;
    assert!(resp.is_ok());
    assert_eq!(
        resp.unwrap().status(),
        http::status::StatusCode::OK.as_u16()
    );

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_cannot_serve_http_requests() {
    init_logger();

    // Start a runtime with an HTTP server node. The HTTP server in this case rejects the requests,
    // and would not send anything to the Oak node. Creating a thread to simulate the Oak node will
    // result in the thread being blocked for ever. So, we set up the test without an
    // oak-node-simulator thread.
    let mut http_server_tester = HttpServerTester::new(2526, 0);
    let client_with_valid_tls = create_client(LOCAL_CA);

    // Send an HTTP request, and check that the server responds with an error
    let resp = send_request(client_with_valid_tls, "http://localhost:2526").await;
    assert!(resp.is_err());

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_does_not_terminate_after_a_bad_request() {
    init_logger();

    // Start a runtime with an HTTP server node, and a thread simulating an Oak node to respond to
    // HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2527, 2);
    let client_with_valid_tls = create_client(LOCAL_CA);
    let client_with_invalid_tls = create_client(GCP_CA);

    // Send a valid request, making sure that the server is started
    let resp = send_request(client_with_valid_tls.clone(), "https://localhost:2527").await;
    assert!(resp.is_ok());

    // Send an HTTPS request with invalid certificate, and check that the server responds with error
    let resp = send_request(client_with_invalid_tls, "https://localhost:2527").await;
    assert!(resp.is_err());

    // Send another valid request, and check that the server is alive and responsive
    // let client_with_valid_tls = create_client(LOCAL_CA);
    let resp = send_request(client_with_valid_tls, "https://localhost:2527").await;
    assert!(resp.is_ok());

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

fn create_runtime() -> RuntimeProxy {
    let configuration = ApplicationConfiguration {
        wasm_modules: hashmap! {},
        initial_node_configuration: None,
    };
    let signature_table = crate::SignatureTable::default();
    info!("Create runtime for test");

    crate::RuntimeProxy::create_runtime(
        &configuration,
        &crate::SecureServerConfiguration::default(),
        &signature_table,
    )
}

fn create_server_node(port: u32) -> Box<HttpServerNode> {
    let tls_config = crate::tls::TlsConfig::new(
        "../examples/certs/local/local.pem",
        "../examples/certs/local/local.key",
    )
    .expect("Could not create TLS config from local certs.");

    // Create http server node
    Box::new(
        HttpServerNode::new(
            "test-node",
            HttpServerConfiguration {
                address: format!("[::]:{}", port),
            },
            tls_config,
        )
        .expect("Could not create server node"),
    )
}

fn create_communication_channel(runtime: &RuntimeProxy) -> (oak_abi::Handle, oak_abi::Handle) {
    // create channel: one end to server_node::run; the other to the Oak node.
    let (init_sender, init_receiver) = runtime
        .channel_create(&Label::public_untrusted())
        .expect("Could not create channel");

    // At the start the HTTP server pseudo-Node expects to receive an invocation channel, with
    // exactly one handle in it.
    //
    // Create a channel for receiving invocations to pass to the HTTP server pseudo-Node.
    let (invocation_sender, invocation_receiver) = runtime
        .channel_create(&Label::public_untrusted())
        .expect("Could not create channel");
    let invocation_sender = HttpInvocationSender {
        sender: Some(Sender::<HttpInvocation>::new(WriteHandle {
            handle: invocation_sender,
        })),
    };
    let init_sender = Sender::<HttpInvocationSender>::new(WriteHandle {
        handle: init_sender,
    });

    if let Err(error) = init_sender.send(invocation_sender, runtime) {
        panic!("Could not write to the `init_sender` channel: {}", error);
    }
    if let Err(error) = init_sender.close(runtime) {
        panic!("Could not close the `init_sender` channel: {}", error);
    }

    (init_receiver, invocation_receiver)
}

// Simulate an Oak node that responds to the specified number of requests. Since the Oak node blocks
// until a new request is received, we need to know the number of requests that the test sends
// beforehand. Alternatively, the node simulator could listen for incoming requests in an infinite
// loop and have a termination mechanism that could be signalled from outside. However, specifying
// the exact number of expected requests is more appropriate for testing purposes.
fn oak_node_simulator(
    number_of_requests: i32,
    runtime: &RuntimeProxy,
    invocation_receiver: oak_abi::Handle,
) {
    // Get invocation message that contains the response_writer handle.
    let invocation_receiver = Receiver::<HttpInvocation>::new(ReadHandle {
        handle: invocation_receiver,
    });

    for _counter in 0..number_of_requests {
        let invocation = invocation_receiver.receive(runtime).unwrap();
        let resp = HttpResponse {
            body: vec![],
            status: http::status::StatusCode::OK.as_u16() as i32,
            headers: hashmap! {},
        };
        invocation
            .sender
            .expect("Empty sender on invocation.")
            .send(resp, runtime)
            .unwrap();
    }
}

// Build a TLS client, using the given CA store
fn create_client(
    ca_path: &str,
) -> hyper::client::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>> {
    let ca_file =
        fs::File::open(ca_path).unwrap_or_else(|e| panic!("failed to open {}: {}", ca_path, e));
    let mut ca = io::BufReader::new(ca_file);

    // Build an HTTP connector which supports HTTPS too.
    let mut http = hyper::client::HttpConnector::new();
    http.enforce_http(false);
    // Build a TLS client, using the custom CA store for lookups.
    let mut tls = rustls::ClientConfig::new();
    tls.root_store
        .add_pem_file(&mut ca)
        .expect("failed to load custom CA store");
    // Join the above part into an HTTPS connector.
    let https = hyper_rustls::HttpsConnector::from((http, tls));

    hyper::client::Client::builder().build(https)
}

async fn send_request(
    client: hyper::client::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>>,
    uri: &str,
) -> Result<http::response::Response<hyper::Body>, hyper::Error> {
    // Send a request, and wait for the response
    let label = oak_abi::label::Label::public_untrusted();
    let mut label_bytes = vec![];
    if let Err(err) = label.encode(&mut label_bytes) {
        panic!("Failed to encode label: {}", err);
    }

    // The client thread may start sending the requests before the server is up. In this case, the
    // request will be rejected with a "ConnectError". To make the tests are stable, we need to
    // retry sending the requests until the server is up. To distinguish between these cases and
    // actual errors (e.g., errors due to invalid TLS certificates), we need to check the cause of
    // the error.
    loop {
        let request = hyper::Request::builder()
            .method(http::Method::GET)
            .uri(uri)
            .header(oak_abi::OAK_LABEL_HTTP_PROTOBUF_KEY, label_bytes.clone())
            .body(hyper::Body::empty())
            .unwrap();

        match client.request(request).await {
            Ok(reps) => return Ok(reps),
            Err(error) => {
                // We cannot access the cause of the error, so we need to check the string instead.
                let error_str = format!("{:?}", error);
                // If the cause is `ConnectError` (https://github.com/hyperium/hyper/blob/66fc127c8d4f81aed9300c9d0f13246b8206067a/src/client/connect/http.rs#L392)
                // it means that a connection to the server cannot be made. Retry sending the
                // request in this case.
                if error_str.contains("ConnectError") {
                    continue;
                } else {
                    return Err(error);
                }
            }
        }
    }
}
