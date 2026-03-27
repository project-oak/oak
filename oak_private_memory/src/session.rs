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

//! Unified session abstraction over TLS encryption protocols.
//!
//! This module provides a protocol-agnostic wrapper around `oak_session_tls`
//! for encrypting and decrypting application messages *after* the handshake has
//! completed.
//!
//! - [`TlsEncryptedSession`]: wraps an `oak_session_tls::OakSessionTls` using
//!   TLS (via rustls) for encryption.
//!
//! The handshake phase is protocol-specific and is handled separately using
//! `OakSessionTlsInitializer` in the service layer.

use anyhow::{Result, anyhow};
use oak_session_tls::{OakSessionTls, SessionError};

/// Wraps an `oak_session_tls::OakSessionTls` (TLS via rustls) to implement
/// [`EncryptedSession`].
///
/// The TLS session operates directly on raw byte slices, so no additional
/// protobuf serialization is needed.
///
/// This wrapper is created after the TLS handshake completes via
/// `OakSessionTlsInitializer::get_open_session()`.
pub struct TlsEncryptedSession {
    session: OakSessionTls,
}

impl TlsEncryptedSession {
    /// Creates a new `TlsEncryptedSession` from an open `OakSessionTls`.
    pub fn new(session: OakSessionTls) -> Self {
        Self { session }
    }
}

impl TlsEncryptedSession {
    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        self.session.encrypt(plaintext).map_err(|e: SessionError| anyhow!("TLS encrypt: {}", e))
    }

    pub fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>> {
        self.session.decrypt(ciphertext).map_err(|e: SessionError| anyhow!("TLS decrypt: {}", e))
    }
}
