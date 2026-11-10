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

//! Simulated lease-based row lock for `UnencryptedDataBlobs`, mirroring
//! the host implementation in
//! `gdm/privacy/private_memory/untrusted/spanner/db.cc`.

use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use tokio::sync::Mutex;

pub const DEFAULT_LOCK_DURATION: Duration = Duration::from_secs(60);
pub const MAX_LOCK_DURATION: Duration = Duration::from_secs(600);
pub const CLOCK_SKEW_MARGIN: Duration = Duration::from_secs(5);

#[derive(Debug, PartialEq, Eq)]
pub enum LockError {
    InvalidArgument(&'static str),
    NotFound,
    Conflict,
}

struct Lease {
    token: String,
    expires_at: SystemTime,
}

impl Lease {
    fn is_held_by(&self, token: &str, now: SystemTime) -> bool {
        !token.is_empty() && self.token == token && self.expires_at > now
    }

    fn is_locked_at(&self, now: SystemTime) -> bool {
        self.expires_at + CLOCK_SKEW_MARGIN > now
    }
}

/// Simulated lease-based row lock state on `UnencryptedDataBlobs` using a
/// deterministic fake clock (`now` / `advance`).
#[derive(Default)]
pub struct LockState {
    leases: Mutex<HashMap<String, Lease>>,
    rejections: AtomicU64,
    next_token: AtomicU64,
    clock_offset: std::sync::Mutex<Duration>,
}

impl LockState {
    pub fn new() -> Arc<Self> {
        Arc::new(Self::default())
    }

    pub async fn lock(&self, id: &str) {
        let token = self.mint_token();
        self.leases
            .lock()
            .await
            .insert(id.to_string(), Lease { token, expires_at: self.now() + MAX_LOCK_DURATION });
    }

    pub async fn unlock(&self, id: &str) {
        self.leases.lock().await.remove(id);
    }

    pub async fn clear(&self) {
        self.leases.lock().await.clear();
    }

    pub fn now(&self) -> SystemTime {
        UNIX_EPOCH + *self.clock_offset.lock().unwrap()
    }

    pub fn advance(&self, by: Duration) {
        *self.clock_offset.lock().unwrap() += by;
    }

    pub fn rejections(&self) -> u64 {
        self.rejections.load(Ordering::Relaxed)
    }

    pub async fn held_token(&self, id: &str) -> Option<String> {
        let now = self.now();
        self.leases
            .lock()
            .await
            .get(id)
            .filter(|lease| lease.expires_at > now)
            .map(|lease| lease.token.clone())
    }

    pub fn lease_duration(requested: Option<prost_types::Duration>) -> Result<Duration, LockError> {
        let Some(requested) = requested else {
            return Ok(DEFAULT_LOCK_DURATION);
        };
        if requested.seconds == 0 && requested.nanos == 0 {
            return Ok(DEFAULT_LOCK_DURATION);
        }
        let duration = Duration::try_from(requested)
            .map_err(|_| LockError::InvalidArgument("lock_duration must be positive"))?;
        Ok(duration.min(MAX_LOCK_DURATION))
    }

    pub async fn acquire(
        &self,
        id: &str,
        duration: Duration,
        row_exists: bool,
    ) -> Result<(String, SystemTime), LockError> {
        if !row_exists {
            return Err(LockError::NotFound);
        }
        let now = self.now();
        let mut leases = self.leases.lock().await;
        if leases.get(id).is_some_and(|lease| lease.is_locked_at(now)) {
            return Err(LockError::Conflict);
        }
        let token = self.mint_token();
        let expires_at = now + duration;
        leases.insert(id.to_string(), Lease { token: token.clone(), expires_at });
        Ok((token, expires_at))
    }

    pub async fn extend(
        &self,
        id: &str,
        token: &str,
        duration: Duration,
        row_exists: bool,
    ) -> Result<SystemTime, LockError> {
        if token.is_empty() {
            return Err(LockError::InvalidArgument("lock_token must not be empty"));
        }
        if !row_exists {
            return Err(LockError::NotFound);
        }
        let now = self.now();
        let mut leases = self.leases.lock().await;
        match leases.get_mut(id) {
            Some(lease) if lease.is_held_by(token, now) => {
                lease.expires_at = now + duration;
                Ok(lease.expires_at)
            }
            _ => Err(LockError::Conflict),
        }
    }

    pub async fn release(&self, id: &str, token: &str, row_exists: bool) -> Result<(), LockError> {
        if token.is_empty() {
            return Err(LockError::InvalidArgument("lock_token must not be empty"));
        }
        if !row_exists {
            return Err(LockError::NotFound);
        }
        let mut leases = self.leases.lock().await;
        match leases.get(id) {
            None => Ok(()),
            Some(lease) if lease.token == token => {
                leases.remove(id);
                Ok(())
            }
            Some(_) => Err(LockError::Conflict),
        }
    }

    pub async fn rejects_write(&self, id: &str, token: &str, row_exists: bool) -> bool {
        if !row_exists {
            return false;
        }
        let now = self.now();
        let leases = self.leases.lock().await;
        let rejected = match (leases.get(id), token.is_empty()) {
            (None, true) => false,
            (None, false) => true,
            (Some(lease), true) => lease.is_locked_at(now),
            (Some(lease), false) => !lease.is_held_by(token, now),
        };
        if rejected {
            self.rejections.fetch_add(1, Ordering::Relaxed);
        }
        rejected
    }

    fn mint_token(&self) -> String {
        format!("lock-token-{}", self.next_token.fetch_add(1, Ordering::Relaxed))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ID: &str = "row";
    const LEASE: Duration = Duration::from_secs(30);
    const SECOND: Duration = Duration::from_secs(1);

    async fn acquire(state: &LockState) -> Result<String, LockError> {
        state.acquire(ID, LEASE, true).await.map(|(token, _)| token)
    }

    #[test]
    fn lease_duration_follows_the_host() {
        let proto = |seconds, nanos| Some(prost_types::Duration { seconds, nanos });
        assert_eq!(LockState::lease_duration(None), Ok(DEFAULT_LOCK_DURATION));
        assert_eq!(LockState::lease_duration(proto(0, 0)), Ok(DEFAULT_LOCK_DURATION));
        assert_eq!(LockState::lease_duration(proto(30, 0)), Ok(LEASE));
        assert_eq!(LockState::lease_duration(proto(3600, 0)), Ok(MAX_LOCK_DURATION));
        assert!(matches!(
            LockState::lease_duration(proto(-1, 0)),
            Err(LockError::InvalidArgument(_))
        ));
        assert!(matches!(
            LockState::lease_duration(proto(0, -1)),
            Err(LockError::InvalidArgument(_))
        ));
    }

    #[tokio::test]
    async fn acquire_requires_an_existing_row() {
        let state = LockState::default();
        assert_eq!(state.acquire(ID, LEASE, false).await, Err(LockError::NotFound));
    }

    #[tokio::test]
    async fn acquire_is_exclusive() {
        let state = LockState::default();
        acquire(&state).await.unwrap();
        assert_eq!(acquire(&state).await, Err(LockError::Conflict));
    }

    #[tokio::test]
    async fn expired_lock_stays_closed_for_the_clock_skew_margin() {
        let state = LockState::default();
        let token = acquire(&state).await.unwrap();

        state.advance(LEASE + SECOND);
        // The holder has lost it...
        assert!(state.rejects_write(ID, &token, true).await);
        assert_eq!(state.held_token(ID).await, None);
        // ...but nobody else gets in yet.
        assert_eq!(acquire(&state).await, Err(LockError::Conflict));
        assert!(state.rejects_write(ID, "", true).await);

        state.advance(CLOCK_SKEW_MARGIN);
        assert!(!state.rejects_write(ID, "", true).await);
        assert!(acquire(&state).await.is_ok());
    }

    #[tokio::test]
    async fn lock_expires_exactly_at_its_expire_time() {
        let state = LockState::default();
        let token = acquire(&state).await.unwrap();
        state.advance(LEASE - SECOND);
        assert!(!state.rejects_write(ID, &token, true).await);
        state.advance(SECOND);
        assert!(state.rejects_write(ID, &token, true).await);
    }

    #[tokio::test]
    async fn gated_writes() {
        let state = LockState::default();
        // Unlocked row: untokened writes pass, a token naming no lease fails.
        assert!(!state.rejects_write(ID, "", true).await);
        assert!(state.rejects_write(ID, "stale", true).await);

        let token = acquire(&state).await.unwrap();
        assert!(!state.rejects_write(ID, &token, true).await);
        assert!(state.rejects_write(ID, "", true).await);
        assert!(state.rejects_write(ID, "other", true).await);
        assert_eq!(state.rejections(), 3);
    }

    #[tokio::test]
    async fn missing_row_is_always_writable() {
        let state = LockState::default();
        assert!(!state.rejects_write(ID, "", false).await);
        assert!(!state.rejects_write(ID, "any-token", false).await);
    }

    #[tokio::test]
    async fn extend_replaces_the_expiry() {
        let state = LockState::default();
        let token = acquire(&state).await.unwrap();
        state.advance(LEASE - SECOND);
        let expires_at = state.extend(ID, &token, LEASE, true).await.unwrap();
        assert_eq!(expires_at, state.now() + LEASE);
    }

    #[tokio::test]
    async fn extend_refuses_lost_leases() {
        let state = LockState::default();
        let token = acquire(&state).await.unwrap();
        assert_eq!(state.extend(ID, "other", LEASE, true).await, Err(LockError::Conflict));
        state.advance(LEASE);
        assert_eq!(state.extend(ID, &token, LEASE, true).await, Err(LockError::Conflict));
    }

    #[tokio::test]
    async fn extend_and_release_validate_arguments() {
        let state = LockState::default();
        assert!(matches!(
            state.extend(ID, "", LEASE, true).await,
            Err(LockError::InvalidArgument(_))
        ));
        assert!(matches!(state.release(ID, "", true).await, Err(LockError::InvalidArgument(_))));
        assert_eq!(state.extend(ID, "t", LEASE, false).await, Err(LockError::NotFound));
        assert_eq!(state.release(ID, "t", false).await, Err(LockError::NotFound));
    }

    #[tokio::test]
    async fn release_reopens_the_row_immediately() {
        let state = LockState::default();
        let token = acquire(&state).await.unwrap();
        state.advance(LEASE);
        // Lapsed but not taken over: the holder can still release, and the
        // row reopens without waiting out the clock-skew margin.
        assert_eq!(state.release(ID, &token, true).await, Ok(()));
        assert!(acquire(&state).await.is_ok());
    }

    #[tokio::test]
    async fn release_is_idempotent_but_not_for_other_holders() {
        let state = LockState::default();
        assert_eq!(state.release(ID, "t", true).await, Ok(()));
        let token = acquire(&state).await.unwrap();
        assert_eq!(state.release(ID, "other", true).await, Err(LockError::Conflict));
        assert_eq!(state.release(ID, &token, true).await, Ok(()));
        assert_eq!(state.release(ID, &token, true).await, Ok(()));
    }

    #[tokio::test]
    async fn late_release_cannot_clear_a_new_holder() {
        let state = LockState::default();
        let old = acquire(&state).await.unwrap();
        state.advance(LEASE + CLOCK_SKEW_MARGIN);
        let new = acquire(&state).await.unwrap();
        assert_eq!(state.release(ID, &old, true).await, Err(LockError::Conflict));
        assert_eq!(state.held_token(ID).await, Some(new));
    }
}
