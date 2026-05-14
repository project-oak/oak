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

//! Rust wrapper around tink-cc's ML-DSA-44 implementation.
//!
//! Provides signing, verification, and key generation for
//! [ML-DSA-44 (FIPS 204)](https://csrc.nist.gov/pubs/fips/204/final)
//! using raw key bytes. The underlying implementation delegates to
//! tink-cc (which in turn uses BoringSSL) via C FFI.
//!
//! Tink internally uses an empty context string for ML-DSA operations,
//! which matches the FIPS 204 default.

use alloc::{string::String, vec::Vec};

use cxx_string::CxxString;
use oak_ffi_bytes::BytesView;

/// Size of an ML-DSA-44 public key in bytes.
pub const PUBLIC_KEY_BYTES: usize = 1312;
/// Size of an ML-DSA-44 signature in bytes.
pub const SIGNATURE_BYTES: usize = 2420;

/// Error type for ML-DSA-44 operations.
#[derive(Debug, thiserror::Error)]
pub enum MlDsa44Error {
    #[error("invalid public key length: expected {PUBLIC_KEY_BYTES}, got {0}")]
    InvalidPublicKeyLength(usize),
    #[error("invalid signature length: expected {SIGNATURE_BYTES}, got {0}")]
    InvalidSignatureLength(usize),
    #[error("signing failed: {0}")]
    SigningFailed(String),
    #[error("key generation failed: {0}")]
    KeyGenerationFailed(String),
}

// ── FFI types ──────────────────────────────────────────────────────────

#[repr(C)]
struct StatusWrapper {
    status_code: i32,
    status_message: CxxString,
}

#[repr(C)]
struct MlDsa44SignResult {
    status_code: i32,
    status_message: CxxString,
    signature: CxxString,
}

#[repr(C)]
struct MlDsa44KeyGenResult {
    status_code: i32,
    status_message: CxxString,
    public_key: CxxString,
    private_key: CxxString,
}

#[link(name = "ml_dsa_44-ffi")]
unsafe extern "C" {
    fn MlDsa44Verify(
        message: BytesView,
        signature: BytesView,
        raw_public_key: BytesView,
    ) -> StatusWrapper;

    fn MlDsa44Sign(
        message: BytesView,
        raw_private_key: BytesView,
        raw_public_key: BytesView,
    ) -> MlDsa44SignResult;

    fn MlDsa44KeyGen() -> MlDsa44KeyGenResult;
}

// ── Public types ───────────────────────────────────────────────────────

/// An ML-DSA-44 verifying (public) key.
///
/// Wraps 1312 raw bytes as defined by
/// [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    raw: Vec<u8>,
}

impl VerifyingKey {
    /// Verifies an ML-DSA-44 `signature` over `message`.
    ///
    /// Returns `true` if the signature is valid, `false` otherwise.
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        let status = unsafe {
            MlDsa44Verify(
                BytesView::new_from_slice(message),
                BytesView::new_from_slice(&signature.raw),
                BytesView::new_from_slice(&self.raw),
            )
        };
        status.status_code == 0
    }
}

impl TryFrom<&[u8]> for VerifyingKey {
    type Error = MlDsa44Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != PUBLIC_KEY_BYTES {
            return Err(MlDsa44Error::InvalidPublicKeyLength(bytes.len()));
        }
        Ok(Self { raw: bytes.to_vec() })
    }
}

impl AsRef<[u8]> for VerifyingKey {
    fn as_ref(&self) -> &[u8] {
        &self.raw
    }
}

/// An ML-DSA-44 signature.
///
/// Wraps 2420 raw bytes as defined by
/// [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    raw: Vec<u8>,
}

impl TryFrom<&[u8]> for Signature {
    type Error = MlDsa44Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != SIGNATURE_BYTES {
            return Err(MlDsa44Error::InvalidSignatureLength(bytes.len()));
        }
        Ok(Self { raw: bytes.to_vec() })
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.raw
    }
}

/// An ML-DSA-44 key pair for signing and verification.
///
/// Holds both the raw private key bytes and the corresponding
/// [`VerifyingKey`]. Private key bytes are kept in memory only while
/// the `KeyPair` is alive.
pub struct KeyPair {
    private_key: Vec<u8>,
    verifying_key: VerifyingKey,
}

impl KeyPair {
    /// Returns a reference to the verifying (public) key.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.verifying_key
    }

    /// Signs `message` with the private key.
    pub fn sign(&self, message: &[u8]) -> Result<Signature, MlDsa44Error> {
        let result = unsafe {
            MlDsa44Sign(
                BytesView::new_from_slice(message),
                BytesView::new_from_slice(&self.private_key),
                BytesView::new_from_slice(&self.verifying_key.raw),
            )
        };
        if result.status_code != 0 {
            return Err(MlDsa44Error::SigningFailed(
                String::from_utf8_lossy(result.status_message.as_slice()).into_owned(),
            ));
        }
        Ok(Signature { raw: result.signature.as_slice().to_vec() })
    }
}

/// Generates a fresh ML-DSA-44 key pair.
pub fn generate_key_pair() -> Result<KeyPair, MlDsa44Error> {
    let result = unsafe { MlDsa44KeyGen() };
    if result.status_code != 0 {
        return Err(MlDsa44Error::KeyGenerationFailed(
            String::from_utf8_lossy(result.status_message.as_slice()).into_owned(),
        ));
    }
    let public_key_bytes = result.public_key.as_slice().to_vec();
    let private_key_bytes = result.private_key.as_slice().to_vec();
    Ok(KeyPair {
        verifying_key: VerifyingKey { raw: public_key_bytes },
        private_key: private_key_bytes,
    })
}
