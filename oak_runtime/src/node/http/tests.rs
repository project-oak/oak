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

use crate::{
    io::{channel_create, ReceiverExt, SenderExt},
    node::{http::util::Pipe, CreatedNode, Node, NodeIsolation},
    permissions::PermissionsConfiguration,
    proto::oak::invocation::{HttpInvocation, HttpInvocationSender},
    NodePrivilege, RuntimeProxy,
};
use log::{error, info};
use maplit::hashmap;
use oak_abi::{
    label::{confidentiality_label, public_key_identity_tag, tls_endpoint_tag, Label},
    proto::oak::application::{
        node_configuration::ConfigType, ApplicationConfiguration, HttpClientConfiguration,
        HttpServerConfiguration, NodeConfiguration,
    },
    OakStatus,
};
use oak_io::{handle::ReadHandle, OakError, Receiver};
use oak_services::proto::oak::encap::{HttpRequest, HttpResponse};
use prost::Message;
use std::{fs, io, sync::mpsc};
use tokio::sync::oneshot;

const LOCAL_CA: &str = "../examples/certs/local/ca.pem";
const GCP_CA: &str = "../examples/certs/gcp/ca.pem";

/// A router node that creates a per-request [`EchoNode`] for each incoming request.
struct RouterNode;

impl Node for RouterNode {
    fn node_type(&self) -> &'static str {
        "test-router"
    }
    fn isolation(&self) -> NodeIsolation {
        // Even though this node is not actually sandboxed, we are simulating a Wasm node during
        // testing.
        NodeIsolation::Sandboxed
    }
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        // Get invocation message that contains the response_writer handle.
        let invocation_receiver = Receiver::<HttpInvocation>::new(ReadHandle { handle });

        while let Ok(invocation) = invocation_receiver.receive(&runtime) {
            // Compare the request and response labels. If the echo-node (which gets the
            // request-label) can write to the response-channel, let the `EchoNode` send the
            // response. Otherwise, the RouterNode should send the response to the caller.
            let request_label = invocation
                .clone()
                .receiver
                .unwrap()
                .label(&runtime)
                .unwrap();
            let response_label = invocation.clone().sender.unwrap().label(&runtime).unwrap();
            let can_reply = request_label.flows_to(&response_label);
            let echo_node = EchoNode { can_reply };

            // Create a public init channel to send the invocation to the `EchoNode`.
            let (echo_sender, echo_receiver) =
                channel_create(&runtime, "echo-init", &Label::public_untrusted())
                    .expect("Couldn't create invocation channel");

            // Send the newly created invocation to the request channel.
            echo_sender.send(invocation.clone(), &runtime).unwrap();
            if let Err(error) = echo_sender.close(&runtime) {
                panic!("Couldn't close the `invocation_sender` channel: {}", error);
            }
            runtime
                .node_register(
                    CreatedNode {
                        instance: Box::new(echo_node),
                        privilege: NodePrivilege::default(),
                    },
                    "echo_node",
                    &request_label,
                    echo_receiver.handle.handle,
                )
                .unwrap();

            if !can_reply {
                // If the `EchoNode` cannot respond, send a 200 (OK) response to the user.
                let resp = HttpResponse {
                    body: vec![],
                    status: http::status::StatusCode::OK.as_u16() as i32,
                    headers: None,
                };
                invocation
                    .sender
                    .expect("Empty sender on invocation.")
                    .send(resp, &runtime)
                    .unwrap();
            }
        }
    }
}

/// A simple Oak node that responds with 200 (OK) to every request it receives, and echos the
/// request body and headers in the response.
struct EchoNode {
    can_reply: bool,
}

impl Node for EchoNode {
    fn node_type(&self) -> &'static str {
        "test-echo"
    }
    fn isolation(&self) -> NodeIsolation {
        // Even though this node is not actually sandboxed, we are simulating a Wasm node during
        // testing.
        NodeIsolation::Sandboxed
    }

    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        let invocation_receiver = Receiver::<HttpInvocation>::new(ReadHandle { handle });
        if let Ok(invocation) = invocation_receiver.receive(&runtime) {
            let request = invocation
                .receiver
                .unwrap()
                .receive(&runtime)
                .expect("Couldn't receive the request");

            info!("Got the request: {:?}", request);
            if self.can_reply {
                let resp = HttpResponse {
                    body: request.body,
                    status: http::status::StatusCode::OK.as_u16() as i32,
                    headers: request.headers,
                };
                invocation
                    .sender
                    .expect("Empty sender on invocation.")
                    .send(resp, &runtime)
                    .unwrap();
            }
        }
    }
}

struct HttpServerTester {
    runtime: RuntimeProxy,
}

impl HttpServerTester {
    /// Test setup. Creates an Oak runtime, a test HTTP server node on the given port, and an Oak
    /// node simulator thread.
    fn new(port: u32) -> HttpServerTester {
        let runtime = create_runtime(get_permissions());
        let invocation_receiver =
            create_server_node(&runtime, port).expect("Couldn't create HTTP server node!");
        let _ = env_logger::builder().is_test(true).try_init();

        // Create an Oak node that responds with 200 (OK) to every request it receives.
        runtime
            .node_register(
                CreatedNode {
                    instance: Box::new(RouterNode),
                    privilege: NodePrivilege::default(),
                },
                "oak_node_for_test",
                &Label::public_untrusted(),
                invocation_receiver.handle.handle,
            )
            .expect("Couldn't create Oak node!");

        HttpServerTester { runtime }
    }

    fn cleanup(&mut self) {
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

#[cfg(not(feature = "oak-unsafe"))]
#[test]
fn test_cannot_create_server_node_if_not_permitted() {
    init_logger();
    let runtime = create_runtime(PermissionsConfiguration::default());
    let result = create_server_node(&runtime, 8080);
    assert!(result.is_err())
}

#[cfg(not(feature = "oak-unsafe"))]
#[test]
fn test_cannot_create_insecure_http_client_node_if_not_permitted() {
    init_logger();
    let runtime = create_runtime(PermissionsConfiguration::default());
    let result = create_client_node(&runtime, "".to_string());
    assert!(result.is_err())
}

#[tokio::test]
async fn test_https_server_can_serve_https_requests() {
    init_logger();

    // Start a runtime with an HTTP server node, and a thread simulating an Oak node to respond to
    // HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2525);
    let client_with_valid_tls = create_client(LOCAL_CA);

    // Send an HTTPS request with an empty label, and check that response has StatusCode::OK
    let resp = send_request(
        client_with_valid_tls,
        "https://localhost:2525",
        create_signature(),
        Label::public_untrusted(),
    )
    .await;
    assert!(resp.is_ok());
    let resp = resp.unwrap();
    assert_eq!(resp.status(), http::status::StatusCode::OK.as_u16());
    assert!(resp
        .headers()
        .contains_key(oak_abi::OAK_LABEL_HTTP_PROTOBUF_KEY));

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_cannot_serve_http_requests() {
    init_logger();

    // Start a runtime with an HTTP server node. The HTTP server in this case rejects the requests,
    // and would not send anything to the Oak node.
    let mut http_server_tester = HttpServerTester::new(2526);
    let client_with_valid_tls = create_client(LOCAL_CA);

    // Send an HTTP request with empty label, and check that the server responds with an error
    let resp = send_request(
        client_with_valid_tls,
        "http://localhost:2526",
        create_signature(),
        Label::public_untrusted(),
    )
    .await;
    assert!(resp.is_err());

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_does_not_terminate_after_a_bad_request() {
    init_logger();

    // Start a runtime with an HTTP server node, and a test Oak node to respond to HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2527);
    let client_with_valid_tls = create_client(LOCAL_CA);
    let client_with_invalid_tls = create_client(GCP_CA);

    // Send a valid request, making sure that the server is started
    let resp = send_request(
        client_with_valid_tls.clone(),
        "https://localhost:2527",
        create_signature(),
        Label::public_untrusted(),
    )
    .await;
    assert!(resp.is_ok());

    // Send an HTTPS request with invalid certificate, and check that the server responds with error
    let resp = send_request(
        client_with_invalid_tls,
        "https://localhost:2527",
        create_signature(),
        Label::public_untrusted(),
    )
    .await;
    assert!(resp.is_err());

    // Send another valid request, and check that the server is alive and responsive
    // let client_with_valid_tls = create_client(LOCAL_CA);
    let resp = send_request(
        client_with_valid_tls,
        "https://localhost:2527",
        create_signature(),
        Label::public_untrusted(),
    )
    .await;
    assert!(resp.is_ok());

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_can_serve_https_requests_with_non_empty_request_label() {
    init_logger();

    // Start a runtime with an HTTP server node, and a thread simulating an Oak node to respond to
    // HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2528);
    let client_with_valid_tls = create_client(LOCAL_CA);

    let label = confidentiality_label(tls_endpoint_tag("localhost"));

    // Send an HTTPS request, and check that response has StatusCode::OK
    let resp = send_request(
        client_with_valid_tls,
        "https://localhost:2528",
        create_signature(),
        label,
    )
    .await;
    assert!(resp.is_ok());
    let resp = resp.unwrap();
    assert_eq!(resp.status(), http::status::StatusCode::OK.as_u16());

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[tokio::test]
async fn test_https_server_can_serve_https_requests_with_user_identity_as_request_label() {
    init_logger();

    // Start a runtime with an HTTP server node, and a thread simulating an Oak node to respond to
    // HTTP requests.
    let mut http_server_tester = HttpServerTester::new(2529);
    let client_with_valid_tls = create_client(LOCAL_CA);

    let signature = create_signature();

    let label = confidentiality_label(public_key_identity_tag(&signature.clone().public_key));

    // Send an HTTPS request, and check that response has StatusCode::OK
    let resp = send_request(
        client_with_valid_tls,
        "https://localhost:2529",
        signature,
        label,
    )
    .await;
    assert!(resp.is_ok());
    let resp = resp.unwrap();
    assert_eq!(resp.status(), http::status::StatusCode::OK.as_u16());
    assert!(resp
        .headers()
        .contains_key(oak_abi::OAK_LABEL_HTTP_PROTOBUF_KEY));

    // Stop the runtime and the servers
    http_server_tester.cleanup();
}

#[test]
fn test_https_client_can_handle_https_requests_to_an_external_service() {
    init_logger();

    let runtime = create_runtime(get_permissions());

    // Create an HTTP client pseudo-node to serve requests to `https://www.google.com/`. A valid
    // authority is expected in the URI, so we cannot instead start a server on localhost and use
    // that as the external service. The HTTP client pseudo-node is created with a communication
    // channel. A handle to the read half of the channel is returned. The Oak node will use it
    // to fetch the write handle to an invocation channel for sending the invocations to the
    // HTTP client pseudo-node.
    let authority = "www.google.com";
    let oak_node_init_receiver = create_client_node(&runtime, authority.to_string())
        .expect("Couldn't create HTTP client node!");

    // Create a sync_channel to be notified when the Oak Node is completed.
    let (result_sender, result_receiver) = mpsc::sync_channel(1);

    // Create a test Oak node that sends requests to the HTTP client pseudo-node.
    let client_test_node = ClientTesterNode {
        uri: "https://www.google.com/".to_string(),
        result_sender,
        authority: authority.to_string(),
    };

    // Register the test Oak node in the runtime.
    runtime
        .node_register(
            CreatedNode {
                instance: Box::new(client_test_node),
                // The node requires this privilege to be able to create a [`Pipe`] for interaction
                // with the HTTP client pseudo-node. In a more realistic scenario,
                // such a node should not have a privilege like this, and the
                // [`Pipe`] has to be created by the planner node.
                privilege: crate::node::http::client::get_privilege(authority),
            },
            "client_tester_node",
            &confidentiality_label(tls_endpoint_tag(authority)),
            oak_node_init_receiver.handle.handle,
        )
        .unwrap();

    // Wait for the test Node to complete execution before terminating the Runtime.
    let result_value = result_receiver.recv().expect("test node disconnected");

    assert!(result_value.is_ok());
    let resp = result_value.unwrap();
    // The test uses a self signed certificate. So, we expect an error that is converted to an
    // INTERNAL_SERVER_ERROR response in the HTTP client node.
    assert_eq!(
        resp.status,
        http::StatusCode::INTERNAL_SERVER_ERROR.as_u16() as i32
    );
    runtime.runtime.stop();
}

#[test]
fn test_https_client_can_handle_http_requests_to_an_external_service() {
    init_logger();

    let runtime = create_runtime(get_permissions());
    // This is a public node, so the authority can be empty.
    let empty_authority = "".to_string();
    // Create an HTTP client pseudo-node to serve `HTTP` requests`.
    let oak_node_init_receiver =
        create_client_node(&runtime, empty_authority).expect("Couldn't create HTTP client node!");

    // Create a sync_channel to be notified when the Oak Node is completed.
    let (result_sender, result_receiver) = mpsc::sync_channel(1);

    // Create a test Oak node that sends requests to the HTTP client pseudo-node.
    let client_test_node = ClientTesterNode {
        uri: "http://www.google.com".to_string(),
        result_sender,
        authority: "".to_string(),
    };

    // Register the test Oak node in the runtime.
    runtime
        .node_register(
            CreatedNode {
                instance: Box::new(client_test_node),
                privilege: NodePrivilege::default(),
            },
            "client_tester_node",
            &Label::public_untrusted(),
            oak_node_init_receiver.handle.handle,
        )
        .unwrap();

    // Wait for the test Node to complete execution before terminating the Runtime.
    let result_value = result_receiver.recv().expect("test node disconnected");

    assert!(result_value.is_ok());
    let resp = result_value.unwrap();
    assert_eq!(resp.status, http::StatusCode::OK.as_u16() as i32);
    runtime.runtime.stop();
}

fn create_runtime(permissions: PermissionsConfiguration) -> RuntimeProxy {
    let configuration = ApplicationConfiguration {
        wasm_modules: hashmap! {},
        initial_node_configuration: None,
        module_signatures: vec![],
    };
    let tls_config = crate::tls::TlsConfig::new(
        "../examples/certs/local/local.pem",
        "../examples/certs/local/local.key",
    )
    .expect("Couldn't create TLS config from local certs.");
    let secure_server_config = crate::SecureServerConfiguration {
        grpc_config: None,
        http_config: Some(crate::HttpConfiguration {
            tls_config,
            http_client_root_tls_certificate: crate::tls::Certificate::parse(
                include_bytes!("../../../../examples/certs/local/ca.pem").to_vec(),
            )
            .ok(),
        }),
    };
    let signature_table = crate::SignatureTable::default();
    info!("Create runtime for test");

    crate::RuntimeProxy::create_runtime(
        &configuration,
        &permissions,
        &secure_server_config,
        &signature_table,
        None,
    )
}

fn get_permissions() -> PermissionsConfiguration {
    PermissionsConfiguration {
        allow_http_server_nodes: true,
        allow_insecure_http_egress: true,
        allow_egress_https_authorities: vec!["www.google.com".to_string()],
        ..Default::default()
    }
}

fn create_server_node(
    runtime: &RuntimeProxy,
    port: u32,
) -> Result<Receiver<HttpInvocation>, OakStatus> {
    let (init_receiver, invocation_receiver) = create_communication_channel(runtime);
    let server_config = NodeConfiguration {
        config_type: Some(ConfigType::HttpServerConfig(HttpServerConfiguration {
            address: format!("[::]:{}", port),
        })),
    };

    // TODO(#1631): When we have a separate top for each sub-lattice, this should be changed to
    // the top of the identity sub-lattice.
    let top_label = oak_abi::label::confidentiality_label(oak_abi::label::top());

    runtime.node_create(
        "test_server",
        &server_config,
        &top_label,
        init_receiver.handle.handle,
    )?;

    Ok(invocation_receiver)
}

fn create_communication_channel(
    runtime: &RuntimeProxy,
) -> (Receiver<HttpInvocationSender>, Receiver<HttpInvocation>) {
    // Create channel: one end to server_node::run; the other to the Oak node.
    let (init_sender, init_receiver) = channel_create::<HttpInvocationSender>(
        runtime,
        "HTTP server init",
        &Label::public_untrusted(),
    )
    .expect("Couldn't create channel");

    // At the start the HTTP server pseudo-Node expects to receive an invocation channel, with
    // exactly one handle in it.
    //
    // Create a channel for receiving invocations to pass to the HTTP server pseudo-Node.
    let (invocation_sender, invocation_receiver) = channel_create::<HttpInvocation>(
        runtime,
        "HTTP server invocation",
        &Label::public_untrusted(),
    )
    .expect("Couldn't create channel");
    let http_invocation_sender = HttpInvocationSender {
        sender: Some(invocation_sender),
    };

    if let Err(error) = init_sender.send(http_invocation_sender, runtime) {
        panic!("Couldn't write to the `init_sender` channel: {}", error);
    }
    if let Err(error) = init_sender.close(runtime) {
        panic!("Couldn't close the `init_sender` channel: {}", error);
    }

    (init_receiver, invocation_receiver)
}

// Build a TLS client, using the given CA store
fn create_client(
    ca_path: &str,
) -> hyper::client::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>> {
    let ca_file =
        fs::File::open(ca_path).unwrap_or_else(|e| panic!("Failed to open {}: {}", ca_path, e));
    let mut ca = io::BufReader::new(ca_file);

    // Build an HTTP connector which supports HTTPS too.
    let mut http = hyper::client::HttpConnector::new();
    http.enforce_http(false);
    // Build a TLS client, using the custom CA store for lookups.
    let mut tls = rustls::ClientConfig::new();
    tls.root_store
        .add_pem_file(&mut ca)
        .expect("Failed to load custom CA store");
    // Join the above part into an HTTPS connector.
    let https = hyper_rustls::HttpsConnector::from((http, tls));

    hyper::client::Client::builder().build(https)
}

fn create_signature() -> oak_abi::proto::oak::identity::SignedChallenge {
    let key_pair = oak_sign::KeyPair::generate().unwrap();
    let signature =
        oak_sign::SignatureBundle::create(oak_abi::OAK_CHALLENGE.as_bytes(), &key_pair).unwrap();

    oak_abi::proto::oak::identity::SignedChallenge {
        signed_hash: signature.signed_hash,
        public_key: key_pair.public_key_der().unwrap(),
    }
}

async fn send_request(
    client: hyper::client::Client<hyper_rustls::HttpsConnector<hyper::client::HttpConnector>>,
    uri: &str,
    signature: oak_abi::proto::oak::identity::SignedChallenge,
    request_label: Label,
) -> Result<http::response::Response<hyper::Body>, hyper::Error> {
    // Send a request, and wait for the response
    let mut label_bytes = vec![];
    if let Err(err) = request_label.encode(&mut label_bytes) {
        panic!("Failed to encode label: {}", err);
    }
    let label_bytes = base64::encode(label_bytes);

    let mut sig_bytes = vec![];
    if let Err(err) = signature.encode(&mut sig_bytes) {
        panic!("Failed to encode signature: {}", err);
    }
    let sig_bytes = base64::encode(sig_bytes);

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
            .header(
                oak_abi::OAK_SIGNED_CHALLENGE_HTTP_PROTOBUF_KEY,
                sig_bytes.clone(),
            )
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

/// Creates an HTTP client pseudo-node in the given Runtime.
fn create_client_node(
    runtime: &RuntimeProxy,
    authority: String,
) -> Result<Receiver<HttpInvocationSender>, OakStatus> {
    let label = if authority.is_empty() {
        Label::public_untrusted()
    } else {
        confidentiality_label(tls_endpoint_tag(&authority))
    };
    let (init_receiver, invocation_receiver) = create_http_client_communication_channel(runtime);
    let client_config = NodeConfiguration {
        config_type: Some(ConfigType::HttpClientConfig(HttpClientConfiguration {
            authority,
        })),
    };

    runtime.node_create(
        "test_http_client",
        &client_config,
        &label,
        invocation_receiver.handle.handle,
    )?;

    Ok(init_receiver)
}

/// An HTTP client pseudo-node needs a channel to read `HttpInvocation`s from.
/// We wrap the write half of the channel in an `HttpInvocationSender` and hand it to the Oak node,
/// which will use the write half of the channel to send the requests to the HTTP client
/// pseudo-node.
/// This function creates two channels, and returns their receiver (read) ends. The first receiver
/// will be used as the initial handle to the Oak node. The second receiver is the initial handle
/// to the HTTP client node.
fn create_http_client_communication_channel(
    runtime: &RuntimeProxy,
) -> (Receiver<HttpInvocationSender>, Receiver<HttpInvocation>) {
    // Create HttpInvocation channel: The receiver end goes to the Oak node. The other end goes to
    // the HTTP client pseudo-node.
    let (init_sender, init_receiver) = channel_create::<HttpInvocationSender>(
        runtime,
        "Oak node init",
        &Label::public_untrusted(),
    )
    .expect("Couldn't create channel");

    // Create HttpInvocationSender channel: At the start, the Oak Node expects to receive an
    // invocation channel, with exactly one handle in it.
    //
    // Create a channel for sending invocations to the HTTP client pseudo-Node.
    let (invocation_sender, invocation_receiver) = channel_create::<HttpInvocation>(
        runtime,
        "HTTP client invocation",
        &Label::public_untrusted(),
    )
    .expect("Couldn't create channel");
    let http_invocation_sender = HttpInvocationSender {
        sender: Some(invocation_sender),
    };

    if let Err(error) = init_sender.send(http_invocation_sender, runtime) {
        panic!("Couldn't write to the `init_sender` channel: {}", error);
    }
    if let Err(error) = init_sender.close(runtime) {
        panic!("Couldn't close the `init_sender` channel: {}", error);
    }

    (init_receiver, invocation_receiver)
}

/// Struct representing an Oak node that sends requests to an external server via an HTTP client
/// pseudo-node, collects the response and sends it back to the test method using a `SyncSender`.
struct ClientTesterNode {
    uri: String,
    /// SyncSender to send the response from the external service back to the test method.
    result_sender: mpsc::SyncSender<Result<HttpResponse, OakError>>,
    authority: String,
}

impl Node for ClientTesterNode {
    fn node_type(&self) -> &'static str {
        "client-tester"
    }
    fn isolation(&self) -> NodeIsolation {
        // Even though this node is not actually sandboxed, we are simulating a Wasm node during
        // testing.
        NodeIsolation::Sandboxed
    }
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        // At start-of-day we need/expect to receive a write handle for an invocation channel
        // to use for all subsequent activity.
        let startup_receiver = Receiver::<HttpInvocationSender>::new(ReadHandle { handle });
        let invocation_sender = startup_receiver
            .receive(&runtime)
            .and_then(|invocation_sender| {
                invocation_sender
                    .sender
                    .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))
            })
            .expect("Failed to retrieve invocation channel write handle");
        if let Err(err) = startup_receiver.close(&runtime) {
            error!(
                "Failed to close initial inbound channel {}: {:?}",
                handle, err
            );
        }

        // create request.
        // NOTE: Method is case sensitive.
        let request = HttpRequest {
            uri: self.uri.clone(),
            method: http::Method::GET.to_string(),
            body: vec![],
            headers: None,
        };
        let label = if self.authority.is_empty() {
            Label::public_untrusted()
        } else {
            confidentiality_label(tls_endpoint_tag(&self.authority))
        };
        // create channel
        let pipe = Pipe::new(&runtime, &label, &label).expect("Couldn't create the Pipe");

        // send the request on invocation_sender
        pipe.insert_message(&runtime, request)
            .expect("Couldn't insert HTTP request in the pipe");

        // send the invocation to the HTTP client pseudo-node
        pipe.send_invocation(&runtime, invocation_sender.handle)
            .expect("Couldn't send the invocation");

        // wait for the response to come
        let response = pipe.response_receiver.receive(&runtime);

        pipe.close(&runtime);

        // notify the test
        self.result_sender
            .send(response)
            .expect("could not send the result");
    }
}
