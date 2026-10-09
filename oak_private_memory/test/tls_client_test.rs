//
// Copyright 2026 The Project Oak Authors
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

//! Integration tests for TLS session support.
//!
//! These tests verify that TLS-based sessions work end-to-end: the client
//! connects to the server via the `StartTlsSession` RPC, completes a TLS
//! handshake, then performs encrypted operations (register, key_sync,
//! add_memory, search, etc.).

use std::{
    io::BufReader,
    net::SocketAddr,
    sync::Arc,
    time::{Duration, SystemTime},
};

use client::{PrivateMemoryAppClient, PrivateMemoryTlsClient};
use futures::{SinkExt, StreamExt, channel::mpsc, lock::Mutex};
use oak_session_tls::{
    ClientContextConfig, OakSessionTls, OakSessionTlsClientContext, OakSessionTlsServerContext,
    ServerContextConfig, utils,
};
use private_memory_server_lib::{app::ApplicationConfig, metrics::Metrics};
use private_memory_test_utils::{
    default_test_application_config, start_server_with_tls, start_server_with_tls_and_metrics,
    system_time_to_timestamp,
};
use runfiles::Runfiles;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_client::SealedMemoryServiceClient;
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, LlmViews, TlsSessionFrame},
    prelude::v1::*,
};

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

type TestMetrics = metrics_testing::TestMetrics<Metrics>;

/// Returns [`Metrics`] wired to a private in-memory meter provider, so a test
/// can read back what the server recorded.
fn test_metrics() -> TestMetrics {
    TestMetrics::new(Metrics::new)
}

/// Starts a TLS-enabled server configured by `config_fn` that records into
/// `harness`, and returns its URL along with the join handles that must be
/// kept alive.
async fn start_tls_server_recording_into(
    harness: &TestMetrics,
    config_fn: fn(SocketAddr) -> ApplicationConfig,
) -> (
    String,
    tokio::task::JoinHandle<anyhow::Result<()>>,
    tokio::task::JoinHandle<anyhow::Result<()>>,
    tokio::task::JoinHandle<()>,
) {
    let server_ctx = Arc::new(test_server_context());
    let (addr, server, db, persistence) =
        start_server_with_tls_and_metrics(Some(server_ctx), config_fn, harness.metrics.clone())
            .await
            .unwrap();
    (format!("http://{addr}"), server, db, persistence)
}

/// Resolves a workspace-relative path using the bazel runfiles.
fn resolve_runfile(path: &str) -> std::path::PathBuf {
    let r = Runfiles::create().expect("failed to init runfiles");
    r.rlocation(format!("oak+/{}", path)).expect("failed to resolve runfile")
}

/// Loads a test TLS certificate from a runfiles-relative path.
fn load_test_cert(path: &str) -> rustls_pki_types::CertificateDer<'static> {
    let full_path = resolve_runfile(path);
    utils::load_cert_der(BufReader::new(
        std::fs::File::open(&full_path)
            .unwrap_or_else(|e| panic!("failed to open cert {}: {}", full_path.display(), e)),
    ))
}

/// Loads a test TLS private key from a runfiles-relative path.
fn load_test_key(path: &str) -> rustls_pki_types::PrivateKeyDer<'static> {
    let full_path = resolve_runfile(path);
    utils::load_key_der(BufReader::new(
        std::fs::File::open(&full_path)
            .unwrap_or_else(|e| panic!("failed to open key {}: {}", full_path.display(), e)),
    ))
}

fn test_server_context() -> OakSessionTlsServerContext {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let server_cert = load_test_cert("oak_session/tls/testing/test_server.pem");
    let server_key = load_test_key("oak_session/tls/testing/test_server.key");

    OakSessionTlsServerContext::create(ServerContextConfig {
        tls_identity_provider: utils::create_static_cert_identity_provider(
            server_key,
            vec![server_cert],
        ),
        client_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
        custom_cert_verifier: None,
    })
    .expect("failed to create TLS server context")
}

fn test_client_context() -> OakSessionTlsClientContext {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let client_cert = load_test_cert("oak_session/tls/testing/test_client.pem");
    let client_key = load_test_key("oak_session/tls/testing/test_client.key");

    OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_provider: Some(utils::create_static_trust_anchor_provider(ca_cert)),
        tls_identity_provider: Some(utils::create_static_cert_identity_provider(
            client_key,
            vec![client_cert],
        )),
        custom_cert_verifier: None,
        expected_server_name: None,
    })
    .expect("failed to create TLS client context")
}

/// Verifies that a TLS session can be established and basic operations
/// (register, keysync, add memory, retrieve) work end-to-end.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_session_basic() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) =
        start_tls_server_recording_into(&harness, default_test_application_config).await;
    let pm_uid = "tls_test_user";

    let client_ctx = test_client_context();
    let mut client =
        PrivateMemoryTlsClient::create(&url, pm_uid, TEST_EK, &client_ctx).await.unwrap();

    let memory = Memory {
        id: "".to_string(),
        tags: vec!["tls_tag".to_string()],
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 0.0, 0.0],
                }),
                ..Default::default()
            }],
        }),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let response = client.add_memory(memory).await.unwrap();
    let memory_id = response.id;

    let response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(response.success);
    assert_eq!(response.memory.unwrap().id, memory_id);

    // One handshake, then every frame after it counts towards `total`:
    // registration, key sync, add and get.
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "Handshake")]), 1);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "total")]), 4);
    assert_eq!(snapshot.counter("tls_handshake_failures", &[]), 0);
}

/// Verifies that delete_memory works through a TLS session.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_session_delete() {
    let server_ctx = Arc::new(test_server_context());
    let (addr, _server, _db, _persistence) = start_server_with_tls(Some(server_ctx)).await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "tls_delete_test_user";

    let client_ctx = test_client_context();
    let mut client =
        PrivateMemoryTlsClient::create(&url, pm_uid, TEST_EK, &client_ctx).await.unwrap();

    let memory = Memory {
        id: "".to_string(),
        tags: vec!["tls_delete_tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let memory_id = client.add_memory(memory).await.unwrap().id;

    // Delete the memory.
    let delete_response = client.delete_memory(vec![memory_id.clone()]).await.unwrap();
    assert!(delete_response.success);

    // Verify it's gone.
    let get_response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(!get_response.success);
    assert!(get_response.memory.is_none());
}

/// Verifies that reset_memory works through a TLS session.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_session_reset() {
    let server_ctx = Arc::new(test_server_context());
    let (addr, _server, _db, _persistence) = start_server_with_tls(Some(server_ctx)).await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "tls_reset_test_user";

    let client_ctx = test_client_context();
    let mut client =
        PrivateMemoryTlsClient::create(&url, pm_uid, TEST_EK, &client_ctx).await.unwrap();

    // Add a memory.
    let memory = Memory {
        id: "".to_string(),
        tags: vec!["tls_reset_tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let memory_id = client.add_memory(memory).await.unwrap().id;

    // Reset all memories.
    client.reset_memory().await.unwrap();

    // Verify it's gone.
    let get_response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(!get_response.success);
}

/// Verifies that a Noise session still works when TLS is also enabled on
/// the server.
#[tokio::test(flavor = "multi_thread")]
async fn test_noise_still_works_with_tls_enabled() {
    let server_ctx = Arc::new(test_server_context());
    let (addr, _server, _db, _persistence) = start_server_with_tls(Some(server_ctx)).await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "noise_with_tls_user";

    // Use the standard Noise client to verify it still works when TLS is
    // configured on the server.
    let mut client = client::PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK)
        .await
        .unwrap();

    let memory = Memory {
        id: "".to_string(),
        tags: vec!["noise_tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let response = client.add_memory(memory).await.unwrap();
    let memory_id = response.id;

    let response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(response.success);
}

/// The request and response halves of a raw `StartTlsSession` stream.
struct RawTlsStream {
    requests: mpsc::Sender<TlsSessionFrame>,
    responses: tonic::Streaming<TlsSessionFrame>,
}

/// Buffer size of the request channel; tests send one frame at a time.
const RAW_REQUEST_BUFFER: usize = 10;

/// Opens a raw `StartTlsSession` stream.
async fn open_tls_stream(url: &str) -> RawTlsStream {
    let mut client = SealedMemoryServiceClient::connect(url.to_string()).await.unwrap();
    let (requests, request_stream) = mpsc::channel(RAW_REQUEST_BUFFER);
    let responses = client.start_tls_session(request_stream).await.unwrap().into_inner();
    RawTlsStream { requests, responses }
}

/// Opens a raw `StartTlsSession` stream and completes the TLS handshake, for
/// sending frames that `PrivateMemoryTlsClient` cannot produce.
async fn open_raw_tls_session(url: &str) -> (OakSessionTls, RawTlsStream) {
    // The handshake's send and receive closures both need the stream, so they
    // share it; the lock is async because it is held across `.await`s.
    let transport = Arc::new(Mutex::new(open_tls_stream(url).await));
    let (session, _initial_data) = test_client_context()
        .new_initialized_session(
            |tls_frame| {
                let transport = transport.clone();
                async move {
                    transport.lock().await.requests.send(TlsSessionFrame { tls_frame }).await?;
                    Ok::<_, anyhow::Error>(())
                }
            },
            {
                let transport = transport.clone();
                move || {
                    let transport = transport.clone();
                    async move {
                        let frame = transport.lock().await.responses.next().await.transpose()?;
                        Ok::<_, anyhow::Error>(frame.map(|frame| frame.tls_frame))
                    }
                }
            },
        )
        .await
        .unwrap();
    let stream = Arc::into_inner(transport)
        .expect("handshake closures still hold the transport")
        .into_inner();
    (session, stream)
}

/// A failed TLS handshake is counted, both as a TLS handshake failure and as
/// a failed `Handshake` request.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_handshake_failure_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) =
        start_tls_server_recording_into(&harness, default_test_application_config).await;
    let mut stream = open_tls_stream(&url).await;

    stream
        .requests
        .send(TlsSessionFrame { tls_frame: b"not a TLS record".to_vec() })
        .await
        .unwrap();

    let status = match stream.responses.next().await {
        Some(Err(status)) => status,
        other => panic!("expected the handshake to fail, got {other:?}"),
    };
    assert_eq!(status.code(), tonic::Code::Internal);
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "Handshake")]), 1);
    assert_eq!(snapshot.counter("rpc_failure_count", &[("request_type", "Handshake")]), 1);
    assert_eq!(snapshot.counter("tls_handshake_failures", &[]), 1);
}

/// A frame that cannot be decrypted after the handshake is counted as a
/// decryption failure.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_undecryptable_frame_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) =
        start_tls_server_recording_into(&harness, default_test_application_config).await;
    let (_session, mut stream) = open_raw_tls_session(&url).await;

    stream
        .requests
        .send(TlsSessionFrame { tls_frame: b"not a TLS record".to_vec() })
        .await
        .unwrap();

    let status = loop {
        match stream.responses.next().await {
            // Skip post-handshake frames the server may still send.
            Some(Ok(_)) => continue,
            Some(Err(status)) => break status,
            None => panic!("expected the stream to fail"),
        }
    };
    assert_eq!(status.code(), tonic::Code::InvalidArgument);
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "DecryptionFailure")]), 1);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "total")]), 1);
}

/// A post-handshake frame that decrypts to no application data is counted as
/// an empty TLS frame and does not end the session.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_empty_frame_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) =
        start_tls_server_recording_into(&harness, default_test_application_config).await;
    let (_session, RawTlsStream { mut requests, mut responses }) = open_raw_tls_session(&url).await;

    requests.send(TlsSessionFrame { tls_frame: vec![] }).await.unwrap();
    // Close the request stream; the server ends the response stream once it
    // has processed everything, so the counters are final afterwards.
    drop(requests);
    while let Some(frame) = responses.next().await {
        frame.expect("an empty frame must not fail the stream");
    }

    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "EmptyTlsFrame")]), 1);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "total")]), 1);
}

/// A gRPC decode limit small enough that one oversized frame exceeds it, while
/// every TLS handshake message still fits.
const SMALL_DECODE_LIMIT: usize = 64 * 1024;

/// Server config whose gRPC decode limit is small enough for a test to exceed.
fn config_with_small_decode_limit(db_addr: SocketAddr) -> ApplicationConfig {
    ApplicationConfig {
        max_grpc_decode_size_bytes: SMALL_DECODE_LIMIT,
        ..default_test_application_config(db_addr)
    }
}

/// If a frame after the handshake cannot be received (here, because it
/// exceeds the server's gRPC decode limit), the failure is counted.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_receive_failure_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) =
        start_tls_server_recording_into(&harness, config_with_small_decode_limit).await;
    let (_session, mut stream) = open_raw_tls_session(&url).await;

    stream
        .requests
        .send(TlsSessionFrame { tls_frame: vec![0; 2 * SMALL_DECODE_LIMIT] })
        .await
        .unwrap();

    // The server records the failure, then ends the response stream.
    while let Some(Ok(_)) = stream.responses.next().await {}
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("tls_receive_failures", &[]), 1);
    // The oversized frame never reached the dispatch loop.
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "total")]), 0);
}
