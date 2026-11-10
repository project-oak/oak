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

//! Helpers shared by the unit tests in this crate.

use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
    time::{Duration, SystemTime},
};

use oak_private_memory_database::{
    clock::{SystemClock, system_time_to_timestamp},
    database::{MAX_DATABASE_SIZE, MAX_GRPC_DECODE_SIZE},
};
use private_memory_test_database_server_lib::service::{
    LockState, SealedMemoryDatabaseServiceTestImpl,
};
use sealed_memory_rust_proto::{oak::private_memory::SessionConfig, prelude::v1::*};
use tokio::{net::TcpListener, sync::mpsc};

use crate::{
    MAX_MEMORY_TTL_SECONDS, METADATA_BLANKET_TTL_SECONDS, context::UserSessionContext,
    db_client::SharedDbClient, handler::SealedMemorySessionHandler,
};

/// A valid 256-bit key encryption key shared across all requests in a test.
pub(crate) const TEST_KEK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

/// Starts an in-process test database service and returns its address.
///
/// The service persists blobs in memory for the lifetime of the test, so
/// multiple handlers ("connections") built against the same address share
/// the same underlying storage, mirroring the real deployment where the DB
/// is a separate long-lived service.
pub(crate) async fn start_test_db() -> SocketAddr {
    let listener =
        TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 0)).await.unwrap();
    let db_addr = listener.local_addr().unwrap();
    tokio::spawn(async move {
        let _ = private_memory_test_database_server_lib::service::create(listener).await;
    });
    db_addr
}

pub(crate) async fn start_test_db_with_lock_state(lock_state: Arc<LockState>) -> SocketAddr {
    start_test_db_with_service(Arc::new(SealedMemoryDatabaseServiceTestImpl {
        lock_state,
        ..Default::default()
    }))
    .await
}

pub(crate) async fn start_test_db_with_service(
    service: Arc<
        private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl,
    >,
) -> SocketAddr {
    let listener =
        TcpListener::bind(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), 0)).await.unwrap();
    let db_addr = listener.local_addr().unwrap();
    tokio::spawn(async move {
        let _ = private_memory_test_database_server_lib::service::serve(listener, service).await;
    });
    db_addr
}

/// Builds a handler ("connection") against an already-running test DB.
///
/// The returned `mpsc::UnboundedReceiver` must be held for the duration of
/// the test: dropping it would close the persistence channel that the
/// handler sends to when a session is dropped.
pub(crate) fn connect_handler(
    db_addr: SocketAddr,
) -> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
    connect_handler_with_metrics(db_addr, metrics::get_global_metrics())
}

/// Like [`connect_handler`], but records into `metrics`.
pub(crate) fn connect_handler_with_metrics(
    db_addr: SocketAddr,
    metrics: Arc<metrics::Metrics>,
) -> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
    let (persistence_tx, persistence_rx) = mpsc::unbounded_channel();
    (connect_handler_with_persistence_tx(db_addr, metrics, persistence_tx), persistence_rx)
}

/// Like [`connect_handler_with_metrics`], but sends the session to
/// `persistence_tx` when the handler is dropped.
pub(crate) fn connect_handler_with_persistence_tx(
    db_addr: SocketAddr,
    metrics: Arc<metrics::Metrics>,
    persistence_tx: mpsc::UnboundedSender<UserSessionContext>,
) -> SealedMemorySessionHandler {
    let db_client = Arc::new(SharedDbClient::new(db_addr, MAX_GRPC_DECODE_SIZE, metrics.clone()));
    SealedMemorySessionHandler::new(
        metrics,
        persistence_tx,
        db_client,
        Arc::new(SystemClock),
        MAX_DATABASE_SIZE,
        METADATA_BLANKET_TTL_SECONDS,
        MAX_MEMORY_TTL_SECONDS,
        false,
        vec![],
    )
}

/// Wires up a handler backed by a freshly started in-process test database
/// service (a single "connection" against a private DB).
pub(crate) async fn setup_handler()
-> (SealedMemorySessionHandler, mpsc::UnboundedReceiver<UserSessionContext>) {
    connect_handler(start_test_db().await)
}

pub(crate) fn boot_strap_info() -> KeyDerivationInfo {
    KeyDerivationInfo { kek_salt: b"test_salt".to_vec(), kek_version: 1 }
}

pub(crate) fn registration_request(pm_uid: &str) -> UserRegistrationRequest {
    UserRegistrationRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: TEST_KEK.to_vec(),
        boot_strap_info: Some(boot_strap_info()),
    }
}

pub(crate) fn key_sync_request(
    pm_uid: &str,
    session_config: Option<SessionConfig>,
) -> KeySyncRequest {
    KeySyncRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: TEST_KEK.to_vec(),
        session_config,
    }
}

/// A memory tagged `tag` that expires in an hour.
pub(crate) fn memory_with_tag(tag: &str) -> Memory {
    Memory {
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }
}
