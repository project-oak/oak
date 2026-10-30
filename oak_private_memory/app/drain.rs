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

//! Coordinates a planned shutdown across all sessions of the enclave.
//!
//! Writes are acknowledged before they are persisted: a session's changes are
//! persisted when the client calls `SyncDatabase`, or after the session closes,
//! by the persistence worker. Whatever is unpersisted when the enclave stops is
//! lost. Before stopping it, the untrusted host calls
//! `SealedMemoryHostService.Drain`, which, within the request's timeout:
//!
//! 1. Responds to new sessions and requests with `UNAVAILABLE`.
//! 2. Queues every open session with unpersisted changes for persistence, once
//!    the request running on it (if any) is done.
//! 3. Waits for those persists to finish and reports how they went.

use std::{
    sync::{
        Arc, Mutex, Weak,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use futures::stream::{FuturesUnordered, StreamExt};
use log::{info, warn};
use sealed_memory_rust_proto::oak::private_memory::DrainResponse;
use tokio::{sync::RwLock, time::Instant};

use crate::{context::UserSessionContext, persistence_worker::PersistenceQueue};

/// The live context of one session, shared between its handler and `Drain`.
pub type SessionSlot = RwLock<Option<UserSessionContext>>;

/// Cap on a `Drain` request's timeout.
pub const MAX_DRAIN_TIMEOUT: Duration = Duration::from_secs(900);

/// Ended sessions are pruned from the registry once it has grown by this many
/// entries since the last pruning, to avoid unbounded growth on a long-lived
/// task.
const REGISTRY_PRUNE_SLACK: usize = 256;

/// Knows every open session and whether the enclave is draining. One per
/// service.
#[derive(Default)]
pub struct DrainController {
    draining: AtomicBool,
    registry: Mutex<SessionRegistry>,
}

#[derive(Default)]
struct SessionRegistry {
    sessions: Vec<Weak<SessionSlot>>,
    prune_at: usize,
}

impl DrainController {
    pub fn is_draining(&self) -> bool {
        self.draining.load(Ordering::SeqCst)
    }

    /// Fails with `UNAVAILABLE` once draining has started.
    pub fn refuse_if_draining(&self) -> tonic::Result<()> {
        if self.is_draining() {
            return Err(tonic::Status::unavailable(
                "server is shutting down; retry on another server",
            ));
        }
        Ok(())
    }

    /// Makes `session` known to `Drain`. It is forgotten once dropped.
    pub fn register(&self, session: &Arc<SessionSlot>) {
        let mut registry = self.registry.lock().expect("session registry mutex poisoned");
        if registry.sessions.len() >= registry.prune_at {
            registry.sessions.retain(|session| session.strong_count() > 0);
            registry.prune_at = registry.sessions.len() + REGISTRY_PRUNE_SLACK;
        }
        registry.sessions.push(Arc::downgrade(session));
    }

    /// The sessions that are still open.
    pub fn live_sessions(&self) -> Vec<Arc<SessionSlot>> {
        self.registry
            .lock()
            .expect("session registry mutex poisoned")
            .sessions
            .iter()
            .filter_map(Weak::upgrade)
            .collect()
    }

    /// Starts draining. Returns false if a drain had already started.
    pub fn start_draining(&self) -> bool {
        !self.draining.swap(true, Ordering::SeqCst)
    }

    /// Drains as described in the module docs, for at most `timeout` (capped
    /// at [`MAX_DRAIN_TIMEOUT`]), queueing persists on `persistence`. Only the
    /// first call drains; a later one fails with `FAILED_PRECONDITION`.
    pub async fn drain(
        &self,
        timeout: Duration,
        persistence: &PersistenceQueue,
    ) -> tonic::Result<DrainResponse> {
        if !self.start_draining() {
            return Err(tonic::Status::failed_precondition("drain already in progress"));
        }
        info!("draining: refusing new sessions and requests");
        let deadline = Instant::now() + timeout.min(MAX_DRAIN_TIMEOUT);
        let tracker = persistence.tracker();
        let (saved_before, failed_before) = (tracker.saved(), tracker.failed());

        let mut response = DrainResponse::default();
        let sessions = self.live_sessions();
        let mut pending_takes: FuturesUnordered<_> =
            sessions.iter().map(|session| take_and_queue(session, persistence)).collect();
        let mut taken = 0;
        while let Ok(Some(found)) = tokio::time::timeout_at(deadline, pending_takes.next()).await {
            taken += 1;
            match found {
                Found::Clean => response.sessions_clean += 1,
                Found::Skipped => response.sessions_skipped += 1,
                // Counted as saved, failed or left over by `tracker` below.
                Found::Queued => {}
                Found::NoContext => {}
            }
        }
        // Sessions still running a request at the deadline. Counted as left
        // over, though some may have been clean.
        let busy_at_deadline = sessions.len() - taken;
        let sessions_left_over = busy_at_deadline + tracker.wait_idle(deadline).await;

        response.sessions_saved = (tracker.saved() - saved_before) as i64;
        response.sessions_failed = (tracker.failed() - failed_before) as i64;
        response.sessions_left_over = sessions_left_over as i64;
        if response.sessions_failed == 0 && sessions_left_over == 0 {
            info!("drain complete: {response:?}");
        } else {
            warn!("drain incomplete, unpersisted writes will be lost: {response:?}");
        }
        Ok(response)
    }
}

/// What `take_and_queue` found in a session.
enum Found {
    /// Nothing to persist: the session has not key-synced yet, or its handler
    /// already queued the context on close.
    NoContext,
    /// No unpersisted changes.
    Clean,
    /// The client opted out of persistence on close.
    Skipped,
    Queued,
}

/// Takes the session's context out once the request running on it (if any) is
/// done, and queues it for persistence if it has changes to persist.
async fn take_and_queue(session: &SessionSlot, persistence: &PersistenceQueue) -> Found {
    let Some(context) = session.write().await.take() else {
        return Found::NoContext;
    };
    if !context.database.changed() {
        return Found::Clean;
    }
    if context.disable_persistence_on_close {
        return Found::Skipped;
    }
    // Fails only if the worker has stopped; the context's ticket then counts
    // it as failed.
    if let Err(e) = persistence.enqueue(context) {
        warn!("drain: queueing a session for persistence: {e}");
    }
    Found::Queued
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_forgets_dropped_sessions() {
        let controller = DrainController::default();
        let kept = Arc::new(SessionSlot::default());
        let dropped = Arc::new(SessionSlot::default());
        controller.register(&kept);
        controller.register(&dropped);
        drop(dropped);

        let live = controller.live_sessions();

        assert_eq!(live.len(), 1);
        assert!(Arc::ptr_eq(&live[0], &kept));
    }

    #[test]
    fn registry_prunes_ended_sessions_as_it_grows() {
        let controller = DrainController::default();
        for _ in 0..(2 * REGISTRY_PRUNE_SLACK) {
            controller.register(&Arc::new(SessionSlot::default()));
        }

        let registered = controller.registry.lock().unwrap().sessions.len();

        assert!(registered <= REGISTRY_PRUNE_SLACK + 1, "registry grew to {registered}");
        assert!(controller.live_sessions().is_empty());
    }

    #[test]
    fn only_the_first_drain_starts() {
        let controller = DrainController::default();
        assert!(controller.refuse_if_draining().is_ok());

        assert!(controller.start_draining());
        assert!(!controller.start_draining());

        assert!(controller.is_draining());
        assert_eq!(controller.refuse_if_draining().unwrap_err().code(), tonic::Code::Unavailable);
    }
}
