//
// Copyright 2024 The Project Oak Authors
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

//! This module provides traits and implementations for creating and verifying
//! session bindings. Session bindings are a critical security mechanism that
//! cryptographically link a peer's attestation evidence (and thus its verified
//! identity and trustworthiness) to a specific, ongoing communication session.
//! This prevents replay attacks where valid attestation data from one context
//! might be maliciously presented in another.
//!
//! ## Overview
//!
//! The core idea is that a party, after having its attestation validated by a
//! peer, proves its liveness and active participation in the *current* session.
//! It does this by performing a cryptographic operation (like signing or
//! MACing) over a piece of data unique to this session, typically the hash of
//! all messages exchanged during the session's handshake phase (the "handshake
//! hash"). The key used for this operation is itself derived from, or directly
//! part of, the attestation evidence.
//!
//! ## Key Abstractions and Their Roles
//!
//! - **`SessionBinder` Trait (e.g., `SignatureBinder`)**:
//!   - **Purpose**: Implemented by the party that needs to *create* a session
//!     binding. It takes session-specific data (the `bound_data`, usually the
//!     handshake hash) and produces a cryptographic binding (e.g., a
//!     signature).
//!   - **Why**: This demonstrates that the entity possessing the
//!     attestation-related key is actively participating in *this* session.
//!   - **`SignatureBinder`**: A concrete implementation that uses a
//!     cryptographic `Signer`. It can also incorporate `additional_data` into
//!     the signature input, allowing for further context or domain separation.
//!
//! - **`SessionBindingVerifier` Trait (e.g., `SignatureBindingVerifier`)**:
//!   - **Purpose**: Implemented by the party that needs to *verify* a session
//!     binding received from its peer. It takes the session-specific
//!     `bound_data`, the received `binding`, and checks its validity.
//!   - **Why**: Successful verification confirms that the peer, whose
//!     attestation was previously validated, has indeed bound its identity to
//!     this specific session.
//!   - **`SignatureBindingVerifier`**: A concrete implementation that uses a
//!     cryptographic `Verifier`. It also uses `additional_data` if it was part
//!     of the original signature computation, ensuring consistency.
//!
//! - **`SessionBindingVerifierProvider` Trait (e.g.,
//!   `SignatureBindingVerifierProvider`)**:
//!   - **Purpose**: Acts as a factory to create `SessionBindingVerifier`
//!     instances.
//!   - **Why**: This is crucial because the specific verifier (and the key it
//!     needs, like the peer's public key) is often determined by the contents
//!     of the peer's `AttestationResults`. This provider pattern allows the
//!     session logic to obtain the correct verifier *after* attestation has
//!     been processed.
//!   - **`SignatureBindingVerifierProvider`**: A concrete implementation that
//!     uses a `KeyExtractor` to pull the necessary verification key from the
//!     `AttestationResults` and then constructs a `SignatureBindingVerifier`
//!     with it.

use alloc::{boxed::Box, sync::Arc, vec::Vec};
use core::fmt::Debug;

use anyhow::{anyhow, Error};
use derive_builder::Builder;
#[cfg(test)]
use mockall::automock;
use oak_crypto::{signer::Signer, verifier::Verifier};
use oak_proto_rust::oak::attestation::v1::AttestationResults;
use sha2::Digest;

use crate::key_extractor::KeyExtractor;

/// Trait for objects that can create a cryptographic binding for given data.
///
/// A `SessionBinder` is typically used by a party to prove its possession of a
/// key associated with its attestation by creating a binding (e.g., a
/// signature) over data unique to the current session (e.g., the handshake
/// hash). The `Send + Sync` bounds allow binders to be shared across threads if
/// needed, for example, if they encapsulate an `Arc<Signer>`.
#[cfg_attr(test, automock)]
pub trait SessionBinder: Send + Sync {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8>;
}

/// An implementation of `SessionBinder` that uses a cryptographic `Signer`.
///
/// It creates a signature over the concatenation of the `bound_data` (e.g.,
/// handshake hash) and optional `additional_data`. The `additional_data` can be
/// used for domain separation or to include other context-specific information
/// in the signature.
#[derive(Builder)]
#[builder(no_std)]
#[builder(pattern = "owned")]
pub struct SignatureBinder {
    /// The cryptographic signer used to create the binding.
    /// The `Signer` is boxed to allow for different signing algorithm
    /// implementations. Its lifetime is managed by the `SignatureBinder`
    /// instance.
    signer: Box<dyn Signer>,

    /// Optional additional data to be included in the signature computation.
    /// This data is concatenated with `bound_data` before signing.
    #[builder(default)]
    additional_data: Vec<u8>,
}

impl SignatureBinder {
    /// Creates a new `SignatureBinder` with no additional data.
    pub fn new(signer: Box<dyn Signer>) -> Self {
        Self { signer, additional_data: Vec::new() }
    }

    /// Creates a new `SignatureBinder` with additional data.
    pub fn new_with_additional_data(signer: Box<dyn Signer>, additional_data: Vec<u8>) -> Self {
        Self { signer, additional_data }
    }
}

impl SessionBinder for SignatureBinder {
    /// Signs the concatenation of `bound_data` and `self.additional_data`.
    /// Returns the resulting signature as a `Vec<u8>`.
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        self.signer.sign([bound_data, self.additional_data.as_slice()].concat().as_slice())
    }
}

/// Trait for objects that can verify a cryptographic binding.
///
/// A `SessionBindingVerifier` is used by a party to verify a binding received
/// from a peer. This confirms that the peer possesses the key associated with
/// its claimed (and attested) identity and has bound it to the current session.
/// The `Send` bound allows verifiers to be sent across threads if needed.
#[cfg_attr(test, automock)]
pub trait SessionBindingVerifier: Send + Sync + Debug {
    /// Verifies the `binding` against the `bound_data`.
    ///
    /// `bound_data` is typically the handshake hash of the current session.
    /// `binding` is the cryptographic binding received from the peer.
    /// Returns `Ok(())` if the verification is successful, otherwise an
    /// `Error`. The lifetimes of `bound_data` and `binding` are determined
    /// by the caller.
    fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> Result<(), Error>;
}

/// An implementation of `SessionBindingVerifier` that uses a cryptographic
/// `Verifier`.
///
/// It verifies a signature (the `binding`) over the concatenation of the
/// `bound_data` (e.g., handshake hash) and optional `additional_data`.
#[derive(Builder, Debug)]
#[builder(no_std)]
#[builder(pattern = "owned")]
pub struct SignatureBindingVerifier {
    /// The cryptographic verifier used to check the binding.
    /// The `Verifier` is boxed to allow for different algorithm
    /// implementations. Its lifetime is managed by the
    /// `SignatureBindingVerifier` instance.
    verifier: Box<dyn Verifier>,

    /// Optional additional data that was included in the original signature
    /// computation. This must match the `additional_data` used by the
    /// `SignatureBinder`.
    #[builder(default)]
    additional_data: Vec<u8>,
}

impl SessionBindingVerifier for SignatureBindingVerifier {
    /// Verifies the `binding` (signature) against the concatenation of
    /// `bound_data` and `self.additional_data`.
    fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> Result<(), Error> {
        self.verifier
            .verify([bound_data, self.additional_data.as_slice()].concat().as_slice(), binding)
    }
}

/// Trait for objects that can provide a `SessionBindingVerifier`.
///
/// This factory trait is used to create a `SessionBindingVerifier` dynamically,
/// typically based on information extracted from a peer's `AttestationResults`.
/// This allows the choice of verifier (and its keys) to be deferred until after
/// attestation is complete.
/// The `Send + Sync` bounds allow providers to be shared, e.g., as part of
/// session configuration.
pub trait SessionBindingVerifierProvider: Send + Sync {
    /// Creates a `SessionBindingVerifier` based on the provided
    /// `attestation_results`.
    ///
    /// The `attestation_results` contain the outcome of verifying a peer's
    /// attestation, which may include public keys or other material needed
    /// to configure the verifier. Returns a boxed `SessionBindingVerifier`.
    /// The lifetime of the returned verifier is independent of
    /// `attestation_results` once created, as necessary data is
    /// typically cloned or extracted into it.
    fn create_session_binding_verifier(
        &self,
        attestation_results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>>;
}

/// An implementation of `SessionBindingVerifierProvider` that uses a
/// `KeyExtractor`.
///
/// This provider first uses the `key_extractor` to obtain a verifying key from
/// the `attestation_results`. It then constructs a `SignatureBindingVerifier`
/// configured with this key. This decouples the logic of key extraction from
/// the attestation details from the signature verification mechanism itself.
pub struct SignatureBindingVerifierProvider {
    /// The `KeyExtractor` used to obtain a verification key from attestation
    /// results. This is typically an `Arc` to allow sharing the extractor.
    key_extractor: Arc<dyn KeyExtractor>,
}

impl SignatureBindingVerifierProvider {
    /// Creates a new `SignatureBindingVerifierProvider`.
    ///
    /// `key_extractor` is an `Arc<dyn KeyExtractor>` that will be used to
    /// extract the public key for verification from attestation results.
    /// The provider takes ownership of this `Arc`.
    pub fn new(key_extractor: Arc<dyn KeyExtractor>) -> Self {
        Self { key_extractor }
    }
}

impl SessionBindingVerifierProvider for SignatureBindingVerifierProvider {
    /// Creates a `SignatureBindingVerifier`.
    ///
    /// It first calls `self.key_extractor.extract_verifying_key()` with the
    /// `attestation_results` to get the peer's public key. Then, it builds a
    /// `SignatureBindingVerifier` using this key.
    /// If key extraction or verifier building fails, an error is returned.
    fn create_session_binding_verifier(
        &self,
        attestation_results: &AttestationResults,
    ) -> anyhow::Result<Box<dyn SessionBindingVerifier>> {
        let verifying_key = self.key_extractor.extract_verifying_key(attestation_results)?;
        Ok(Box::new(
            SignatureBindingVerifierBuilder::default()
                .verifier(verifying_key)
                .build()
                .map_err(|err| anyhow!("couldn't build SignatureBindingVerifier: {}", err))?,
        ))
    }
}

/// An INFO string used when calculating the session binding token.
const SESSION_BINDING_INFO_STRING: &[u8; 36] = b"04abb564-eeb9-42b7-8091-4d67cdb4d536";

/// Derives a session binding token combining the data from the session
/// initialization steps to bind the session to the supplied attestations.
///
/// * `attestation_binding_token` - Combined data from the attestation step;
///   binds all supplied evidence to the session.
/// * `handshake_hash` - The hash of the handshake binds the handshake step. It
///   is unique to the established session.
pub fn create_session_binding_token(
    attestation_binding_token: &[u8],
    handshake_hash: &[u8],
) -> Vec<u8> {
    let mut ctx = sha2::Sha256::new();
    ctx.update(attestation_binding_token);
    ctx.update(handshake_hash);
    ctx.update(SESSION_BINDING_INFO_STRING);
    ctx.finalize().to_vec()
}
