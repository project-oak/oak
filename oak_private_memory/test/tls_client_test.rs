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

use std::{io::BufReader, sync::Arc};

use client::{PrivateMemoryAppClient, PrivateMemoryTlsClient};
use oak_session_tls::{
    ClientContextConfig, OakSessionTlsClientContext, OakSessionTlsServerContext,
    ServerContextConfig, utils,
};
use private_memory_test_utils::start_server_with_tls;
use runfiles::Runfiles;
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, LlmViews},
    prelude::v1::*,
};

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

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
        tls_identity_provider: utils::create_static_cert_identity_provider(server_key, server_cert),
        client_trust_anchor_der: Some(ca_cert),
        custom_cert_verifier: None,
    })
    .expect("failed to create TLS server context")
}

fn test_client_context() -> OakSessionTlsClientContext {
    let ca_cert = load_test_cert("oak_session/tls/testing/test_ca.pem");
    let client_cert = load_test_cert("oak_session/tls/testing/test_client.pem");
    let client_key = load_test_key("oak_session/tls/testing/test_client.key");

    OakSessionTlsClientContext::create(ClientContextConfig {
        server_trust_anchor_der: Some(ca_cert),
        tls_identity_provider: Some(utils::create_static_cert_identity_provider(
            client_key,
            client_cert,
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
    let server_ctx = Arc::new(test_server_context());
    let (addr, _server, _db, _persistence) = start_server_with_tls(Some(server_ctx)).await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "tls_test_user";

    let client_ctx = test_client_context();
    let mut client =
        PrivateMemoryTlsClient::create(&url, pm_uid, TEST_EK, &client_ctx).await.unwrap();

    let memory_id = "tls_test_memory";
    let memory = Memory {
        id: memory_id.to_string(),
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
        ..Default::default()
    };

    let response = client.add_memory(memory).await.unwrap();
    assert_eq!(response.id, memory_id);

    let response = client.get_memory_by_id(memory_id, None).await.unwrap();
    assert!(response.success);
    assert_eq!(response.memory.unwrap().id, memory_id);
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

    let memory_id = "tls_delete_memory";
    let memory = Memory {
        id: memory_id.to_string(),
        tags: vec!["tls_delete_tag".to_string()],
        ..Default::default()
    };

    client.add_memory(memory).await.unwrap();

    // Delete the memory.
    let delete_response = client.delete_memory(vec![memory_id.to_string()]).await.unwrap();
    assert!(delete_response.success);

    // Verify it's gone.
    let get_response = client.get_memory_by_id(memory_id, None).await.unwrap();
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
        id: "tls_reset_memory".to_string(),
        tags: vec!["tls_reset_tag".to_string()],
        ..Default::default()
    };
    client.add_memory(memory).await.unwrap();

    // Reset all memories.
    client.reset_memory().await.unwrap();

    // Verify it's gone.
    let get_response = client.get_memory_by_id("tls_reset_memory", None).await.unwrap();
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

    let memory_id = "noise_coexist_memory";
    let memory = Memory {
        id: memory_id.to_string(),
        tags: vec!["noise_tag".to_string()],
        ..Default::default()
    };

    let response = client.add_memory(memory).await.unwrap();
    assert_eq!(response.id, memory_id);

    let response = client.get_memory_by_id(memory_id, None).await.unwrap();
    assert!(response.success);
}
