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
//! `SealedMemoryHostService.Drain`, which stops accepting sessions and
//! requests, persists every open session with unpersisted changes, and waits
//! for the persistence queue to empty.

use std::sync::{
    Arc, Mutex, Weak,
    atomic::{AtomicBool, Ordering},
};

use tokio::sync::RwLock;

use crate::context::UserSessionContext;

/// The live context of one session, shared between its handler and `Drain`.
pub type SessionSlot = RwLock<Option<UserSessionContext>>;

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
