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

//! Unified session abstraction over Noise and TLS encryption protocols.
//!
//! This module defines the [`EncryptedSession`] trait, which provides a
//! protocol-agnostic interface for encrypting and decrypting application
//! messages *after* the handshake has completed.
//!
//! Two implementations are provided:
//!
//! - [`NoiseEncryptedSession`]: wraps an open `oak_session::ServerSession`
//!   using the Noise protocol with Oak attestation.
//! - [`TlsEncryptedSession`]: wraps an `oak_session_tls::OakSessionTls` using
//!   TLS (via rustls) for encryption.
//!
//! The handshake phase is protocol-specific and is handled separately:
//! - Noise handshake is managed via `SessionInitializer` in the service layer.
//! - TLS handshake is managed via `OakSessionTlsInitializer` in the service
//!   layer.
//!
//! After the handshake, the server code operates on `dyn EncryptedSession`,
//! making the transport protocol transparent.

use anyhow::{Context, Result, anyhow};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{ServerSession, Session, channel::SessionChannel};
use oak_session_tls::{OakSessionTls, SessionError};

/// A protocol-agnostic encrypted session.
///
/// After the handshake is complete (regardless of whether it used Noise or
/// TLS), this trait provides a uniform encrypt/decrypt interface for
/// application-level plaintext messages.
pub trait EncryptedSession: Send {
    /// Encrypts a plaintext byte slice and returns the ciphertext bytes.
    ///
    /// For Noise sessions, the returned bytes are a serialized
    /// `SessionResponse`. For TLS sessions, the returned bytes are raw TLS
    /// record data.
    fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>>;

    /// Decrypts a ciphertext byte slice and returns the plaintext bytes.
    ///
    /// For Noise sessions, the input bytes are expected to be a serialized
    /// `SessionRequest`. For TLS sessions, the input bytes are raw TLS record
    /// data.
    fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>>;
}

/// Wraps an open `oak_session::ServerSession` (Noise protocol) to implement
/// [`EncryptedSession`].
///
/// The Noise session uses Oak's `SessionRequest`/`SessionResponse` protobuf
/// messages as its wire format, so this wrapper serializes/deserializes them
/// when converting to/from raw bytes.
///
/// This wrapper should only be used after the handshake is complete (i.e.,
/// `ServerSession::is_open()` returns true). The handshake phase is managed
/// separately using the `SessionInitializer` trait.
pub struct NoiseEncryptedSession {
    session: ServerSession,
}

impl NoiseEncryptedSession {
    /// Creates a new `NoiseEncryptedSession` from an open `ServerSession`.
    pub fn new(session: ServerSession) -> Self {
        Self { session }
    }

    /// Returns a mutable reference to the underlying `ServerSession`.
    ///
    /// Useful for the `SessionInitializer` init flow before the session is
    /// open.
    pub fn session_mut(&mut self) -> &mut ServerSession {
        &mut self.session
    }

    /// Returns `true` if the handshake is complete and the session is open.
    pub fn is_open(&self) -> bool {
        self.session.is_open()
    }
}

impl EncryptedSession for NoiseEncryptedSession {
    fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        let response: SessionResponse =
            self.session.encrypt(plaintext.to_vec()).context("encrypting via Noise")?;
        Ok(prost::Message::encode_to_vec(&response))
    }

    fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>> {
        let request: SessionRequest =
            prost::Message::decode(ciphertext).context("decoding SessionRequest")?;
        self.session.decrypt(request).context("decrypting via Noise")
    }
}

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

impl EncryptedSession for TlsEncryptedSession {
    fn encrypt(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        self.session.encrypt(plaintext).map_err(|e: SessionError| anyhow!("TLS encrypt: {}", e))
    }

    fn decrypt(&mut self, ciphertext: &[u8]) -> Result<Vec<u8>> {
        self.session.decrypt(ciphertext).map_err(|e: SessionError| anyhow!("TLS decrypt: {}", e))
    }
}
