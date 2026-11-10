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

//! DEK rotation: re-encrypts all of a user's memory blobs and the metadata
//! index under a freshly generated DEK and replaces the stored wrapped DEK,
//! without losing writes from concurrent sessions.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use external_db_client::{BlobId, DataBlobHandler};
use log::{error, info, warn};
use metrics::Metrics;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use tokio::time::Instant;
use tonic::{Code, transport::Channel};

use crate::{IntoTonicResult, context::UserSessionContext};

/// Converts the `anyhow` errors of rotation steps into a `tonic::Status` whose
/// code tells the client whether to retry.
trait IntoRotationError<T> {
    /// Fails with `message` and the [`rotation_error_code`] of the error.
    fn into_rotation_error(self, message: &str) -> tonic::Result<T>;
}

impl<T> IntoRotationError<T> for anyhow::Result<T> {
    fn into_rotation_error(self, message: &str) -> tonic::Result<T> {
        match self {
            Ok(value) => Ok(value),
            Err(error) => {
                let code = rotation_error_code(&error);
                Err(error).into_tonic_result(code, message)
            }
        }
    }
}

/// Preserves retryable host status codes (`UNAVAILABLE`, `DEADLINE_EXCEEDED`,
/// `ABORTED`, `RESOURCE_EXHAUSTED`) and maps everything else to `INTERNAL`.
fn rotation_error_code(error: &anyhow::Error) -> Code {
    error
        .chain()
        .find_map(|cause| cause.downcast_ref::<tonic::Status>())
        .map(tonic::Status::code)
        .filter(|code| {
            matches!(
                code,
                Code::Unavailable
                    | Code::DeadlineExceeded
                    | Code::Aborted
                    | Code::ResourceExhausted
            )
        })
        .unwrap_or(Code::Internal)
}

/// How long each row lock lease lasts unless [`LockTiming`] says otherwise.
const DEFAULT_LOCK_LEASE: Duration = Duration::from_secs(90);

/// How long each row lock lease lasts, how often the heartbeat renews it, and
/// how long a rotation may hold the lock in total.
#[derive(Clone, Copy, Debug)]
struct LockTiming {
    lease: Duration,
    heartbeat_interval: Duration,
    /// Kept short enough that, with the lease left behind when renewal stops,
    /// the lock is gone within the 15 minutes a background persist waits out a
    /// locked row before it gives up and drops the session's writes.
    max_hold: Duration,
}

impl Default for LockTiming {
    fn default() -> Self {
        Self {
            lease: DEFAULT_LOCK_LEASE,
            heartbeat_interval: Duration::from_secs(20),
            max_hold: Duration::from_secs(10 * 60),
        }
    }
}

/// Renews the row lock in the background, flags the rotation aborted once the
/// lease is lost, and stops renewing once the lock has been held for
/// [`LockTiming::max_hold`].
struct HeartbeatGuard {
    task_handle: tokio::task::JoinHandle<()>,
    aborted: Arc<AtomicBool>,
    /// When the rotation must be done with the lock: [`LockTiming::max_hold`]
    /// after it was acquired.
    deadline: Instant,
}

impl HeartbeatGuard {
    /// Starts renewing the lock every `timing.heartbeat_interval`. A failed
    /// renewal is retried while at least two intervals of the lease remain. An
    /// `ABORTED` renewal, running out of lease, or reaching `timing.max_hold`
    /// stops the renewals and marks the rotation aborted.
    fn spawn(
        uid: String,
        lock_token: String,
        mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
        metrics: Arc<Metrics>,
        timing: LockTiming,
    ) -> Self {
        let aborted = Arc::new(AtomicBool::new(false));
        let aborted_clone = aborted.clone();
        let hold_deadline = Instant::now() + timing.max_hold;

        let task_handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(timing.heartbeat_interval);
            // The first tick completes immediately; skip it so the first renewal
            // comes one interval after the lock was acquired.
            interval.tick().await;
            let mut last_renewed = Instant::now();
            loop {
                interval.tick().await;
                if Instant::now() >= hold_deadline {
                    error!(
                        "Held the row lock for user {uid} for {:?}; aborting rotation",
                        timing.max_hold
                    );
                    aborted_clone.store(true, Ordering::SeqCst);
                    break;
                }
                let extend =
                    db_client.extend_unencrypted_blob_lock(&uid, &lock_token, timing.lease);
                let outcome = tokio::time::timeout(timing.heartbeat_interval, extend)
                    .await
                    .unwrap_or_else(|_| Err(anyhow::anyhow!("lock extension timed out")));
                let Err(e) = outcome else {
                    last_renewed = Instant::now();
                    continue;
                };
                let lease_revoked = e
                    .downcast_ref::<tonic::Status>()
                    .is_some_and(|status| status.code() == Code::Aborted);
                let lease_has_room =
                    last_renewed.elapsed() + 2 * timing.heartbeat_interval < timing.lease;
                if !lease_revoked && lease_has_room {
                    warn!("Failed to renew row lock for user {uid}, will retry: {e:?}");
                    continue;
                }
                error!("Lost row lock for user {uid}: {e:?}; aborting rotation");
                metrics.inc_dek_rotation_lock_extend_failures();
                aborted_clone.store(true, Ordering::SeqCst);
                break;
            }
        });

        Self { task_handle, aborted, deadline: hold_deadline }
    }

    /// Fails if the rotation must stop before `step`: with `DEADLINE_EXCEEDED`
    /// once the lock has been held for [`LockTiming::max_hold`], or with
    /// `ABORTED` if the lock was lost.
    fn check(&self, step: &str) -> tonic::Result<()> {
        // Checked first: at the deadline the heartbeat also sets `aborted`.
        if Instant::now() >= self.deadline {
            return Err(tonic::Status::deadline_exceeded(format!(
                "row lock held for the maximum time before {step}"
            )));
        }
        if self.aborted.load(Ordering::SeqCst) {
            return Err(tonic::Status::aborted(format!("row lock lost before {step}")));
        }
        Ok(())
    }
}

impl Drop for HeartbeatGuard {
    fn drop(&mut self) {
        self.task_handle.abort();
    }
}

/// Releases the row lock on drop if [`RowLockGuard::release`] was not called
/// (e.g. if the RPC was cancelled).
struct RowLockGuard {
    uid: String,
    lock_token: String,
    db_client: Option<SealedMemoryDatabaseServiceClient<Channel>>,
}

impl RowLockGuard {
    fn new(
        uid: String,
        lock_token: String,
        db_client: SealedMemoryDatabaseServiceClient<Channel>,
    ) -> Self {
        Self { uid, lock_token, db_client: Some(db_client) }
    }

    async fn release(mut self) {
        if let Some(db_client) = self.db_client.take() {
            release_row_lock(db_client, &self.uid, &self.lock_token).await;
        }
    }
}

impl Drop for RowLockGuard {
    fn drop(&mut self) {
        let Some(db_client) = self.db_client.take() else { return };
        let uid = std::mem::take(&mut self.uid);
        let lock_token = std::mem::take(&mut self.lock_token);
        match tokio::runtime::Handle::try_current() {
            Ok(runtime) => {
                runtime.spawn(async move { release_row_lock(db_client, &uid, &lock_token).await });
            }
            Err(_) => warn!("No runtime to release the row lock for user {uid}; it expires"),
        }
    }
}

async fn release_row_lock(
    mut db_client: SealedMemoryDatabaseServiceClient<Channel>,
    uid: &BlobId,
    lock_token: &str,
) {
    if let Err(e) = db_client.release_unencrypted_blob_lock(uid, lock_token).await {
        warn!("Failed to release row lock: {e:?}");
    }
}

/// Acquires the exclusive lock on the user's `UnencryptedDataBlobs` row for
/// `timing.lease` and starts a [`HeartbeatGuard`] that keeps renewing it. Fails
/// with `ABORTED` if another writer holds the lock. Returns the lock token,
/// which the rotation presents on its metadata writes: while the lease holds,
/// other writers can't commit, and the metadata version check catches any
/// write that lands after it lapses.
async fn acquire_row_lock(
    user_context: &mut UserSessionContext,
    metrics: &Arc<Metrics>,
    timing: LockTiming,
) -> tonic::Result<(String, HeartbeatGuard)> {
    let lock = user_context
        .database_service_client
        .acquire_unencrypted_blob_lock(&user_context.uid, timing.lease)
        .await
        .into_rotation_error("failed to acquire row lock")?;

    info!("Acquired row lock for user {}", user_context.uid);
    let heartbeat = HeartbeatGuard::spawn(
        user_context.uid.clone(),
        lock.lock_token.clone(),
        user_context.database_service_client.clone(),
        metrics.clone(),
        timing,
    );
    Ok((lock.lock_token, heartbeat))
}

#[cfg(test)]
mod tests {
    use std::net::SocketAddr;

    use private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl;
    use tokio::sync::mpsc;

    use super::*;
    use crate::{
        handler::SealedMemorySessionHandler,
        test_util::{
            connect_handler, connect_handler_with_metrics, key_sync_request, registration_request,
            start_test_db_with_service,
        },
    };

    type TestMetrics = metrics_testing::TestMetrics<Metrics>;

    struct Setup {
        service: Arc<SealedMemoryDatabaseServiceTestImpl>,
        db_addr: SocketAddr,
        handler: SealedMemorySessionHandler,
        harness: TestMetrics,
        _persistence_rx: mpsc::UnboundedReceiver<UserSessionContext>,
    }

    async fn setup(pm_uid: &str) -> Setup {
        let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        let db_addr = start_test_db_with_service(service.clone()).await;
        let harness = TestMetrics::new(Metrics::new);
        let (handler, _persistence_rx) =
            connect_handler_with_metrics(db_addr, harness.metrics.clone());
        handler.user_registration_handler(registration_request(pm_uid)).await.unwrap();
        handler.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        Setup { service, db_addr, handler, harness, _persistence_rx }
    }

    async fn wait_for_abort(guard: &HeartbeatGuard, timeout: Duration) {
        let deadline = Instant::now() + timeout;
        while guard.check("test").is_ok() {
            assert!(Instant::now() < deadline, "heartbeat did not abort within {timeout:?}");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }

    async fn wait_for_lock_release(service: &SealedMemoryDatabaseServiceTestImpl, pm_uid: &str) {
        let deadline = Instant::now() + Duration::from_secs(10);
        while service.lock_state.held_token(pm_uid).await.is_some() {
            assert!(Instant::now() < deadline, "row lock was not released");
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }

    /// A rotation must give the row back while background persists are still
    /// waiting it out, or they drop their sessions' writes.
    #[test]
    fn lock_is_gone_before_background_persists_give_up() {
        let timing = LockTiming::default();
        // Storage keeps a lapsed lock for a few more seconds of clock skew.
        let skew_margin = Duration::from_secs(5);
        assert!(
            timing.max_hold + timing.lease + skew_margin
                < crate::persistence_worker::BACKGROUND_LOCK_WAIT
        );
    }

    #[test]
    fn into_rotation_error_preserves_only_retryable_host_codes() {
        let code =
            |result: anyhow::Result<()>| result.into_rotation_error("test").unwrap_err().code();
        for retryable in
            [Code::Unavailable, Code::DeadlineExceeded, Code::Aborted, Code::ResourceExhausted]
        {
            let status = tonic::Status::new(retryable, "host");
            assert_eq!(code(Err(anyhow::Error::from(status).context("rpc"))), retryable);
        }
        assert_eq!(code(Err(tonic::Status::not_found("host").into())), Code::Internal);
        assert_eq!(code(Err(anyhow::anyhow!("local failure"))), Code::Internal);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn acquire_row_lock_fails_with_aborted_while_another_session_holds_it() {
        let pm_uid = "contended_lock_user";
        let Setup { service, db_addr, handler, harness, _persistence_rx: _rx } =
            setup(pm_uid).await;
        let (other, _other_rx) = connect_handler(db_addr);
        other.key_sync_handler(key_sync_request(pm_uid, None)).await.unwrap();
        let timing = LockTiming::default();
        let mut guard = handler.session_context().await;
        let (token, _heartbeat) =
            acquire_row_lock(guard.as_mut().unwrap(), &harness.metrics, timing).await.unwrap();

        let mut other_guard = other.session_context().await;
        let result =
            acquire_row_lock(other_guard.as_mut().unwrap(), &harness.metrics, timing).await;

        assert_eq!(result.err().unwrap().code(), Code::Aborted);
        assert_eq!(service.lock_state.held_token(pm_uid).await, Some(token));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn row_lock_guard_release_frees_the_lock() {
        let pm_uid = "release_lock_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (token, heartbeat) =
            acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
        drop(heartbeat);
        let row_lock =
            RowLockGuard::new(ctx.uid.clone(), token, ctx.database_service_client.clone());

        row_lock.release().await;

        assert_eq!(service.lock_state.held_token(pm_uid).await, None);
        acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn dropped_row_lock_guard_frees_the_lock() {
        let pm_uid = "dropped_lock_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (token, heartbeat) =
            acquire_row_lock(ctx, &harness.metrics, LockTiming::default()).await.unwrap();
        drop(heartbeat);
        let row_lock =
            RowLockGuard::new(ctx.uid.clone(), token, ctx.database_service_client.clone());

        drop(row_lock);

        wait_for_lock_release(&service, pm_uid).await;
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_aborts_once_the_lease_is_lost() {
        let pm_uid = "heartbeat_lost_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let timing = LockTiming {
            lease: Duration::from_secs(60),
            heartbeat_interval: Duration::from_millis(10),
            ..LockTiming::default()
        };
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let (_token, heartbeat) = acquire_row_lock(ctx, &harness.metrics, timing).await.unwrap();

        tokio::time::sleep(Duration::from_millis(100)).await;
        assert!(heartbeat.check("test").is_ok());
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);

        service.lock_state.advance(timing.lease + Duration::from_secs(1));
        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;
        assert_eq!(heartbeat.check("step").unwrap_err().code(), Code::Aborted);
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 1);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_aborts_once_the_lock_is_held_for_max_hold() {
        let pm_uid = "max_hold_user";
        let Setup { service, handler, harness, _persistence_rx: _rx, .. } = setup(pm_uid).await;
        let timing = LockTiming {
            heartbeat_interval: Duration::from_millis(10),
            max_hold: Duration::from_millis(200),
            ..LockTiming::default()
        };
        let mut guard = handler.session_context().await;
        let started = Instant::now();
        let (token, heartbeat) =
            acquire_row_lock(guard.as_mut().unwrap(), &harness.metrics, timing).await.unwrap();

        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;

        assert!(started.elapsed() >= timing.max_hold);
        assert_eq!(heartbeat.check("step").unwrap_err().code(), Code::DeadlineExceeded);
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);
        // The lease itself is still held; the rotation releases it.
        assert_eq!(service.lock_state.held_token(pm_uid).await, Some(token));
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn heartbeat_retries_failed_renewals_while_the_lease_allows() {
        let Setup { handler, harness, _persistence_rx: _rx, .. } =
            setup("heartbeat_retry_user").await;
        let timing = LockTiming {
            lease: Duration::from_secs(3),
            heartbeat_interval: Duration::from_millis(200),
            ..LockTiming::default()
        };
        let guard = handler.session_context().await;
        let ctx = guard.as_ref().unwrap();
        let started = Instant::now();
        let heartbeat = HeartbeatGuard::spawn(
            ctx.uid.clone(),
            String::new(),
            ctx.database_service_client.clone(),
            harness.metrics.clone(),
            timing,
        );

        tokio::time::sleep(Duration::from_secs(1)).await;
        assert!(heartbeat.check("test").is_ok(), "gave up while the lease had room");
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 0);
        wait_for_abort(&heartbeat, Duration::from_secs(10)).await;
        assert!(started.elapsed() >= timing.lease - 2 * timing.heartbeat_interval);
        assert_eq!(harness.collect().counter("dek_rotation_lock_extend_failures", &[]), 1);
    }
}
