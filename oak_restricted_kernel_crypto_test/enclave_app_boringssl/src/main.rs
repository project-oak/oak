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

//! Enclave application that exposes AES-GCM AEAD operations via micro_rpc
//! using BoringSSL's safe Rust bindings (`bssl-crypto`).
//!
//! This binary runs under the Oak Restricted Kernel and implements the
//! [`service::oak::crypto_test::Aead`] service using BoringSSL's `bssl-crypto`
//! crate, which provides safe, idiomatic Rust wrappers around the underlying
//! `EVP_AEAD` C API.  It is used by the integration test to exercise the
//! BoringSSL crypto implementation against Wycheproof test vectors.
//!
//! The service is intentionally kept separate from the test so that it can
//! be swapped with the [`aes-gcm`-based enclave app](../enclave_app/) or
//! any other implementation without changing the test itself.
//!
//! ## bssl-crypto AEAD API
//!
//! The AEAD operations use BoringSSL's safe Rust bindings documented at
//! <https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-crypto/src/aead.rs>.
//! Key points:
//!
//! - `Aead::seal` produces `ciphertext || tag` concatenated in a single
//!   `Vec<u8>`.  We split the tag off before returning.
//! - `Aead::open` expects `ciphertext || tag` concatenated as input and returns
//!   `Option<Vec<u8>>`.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use alloc::{boxed::Box, format};

use bssl_crypto::aead::{Aead, Aes128Gcm, Aes256Gcm};
use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, start_blocking_server},
    entrypoint,
    utils::samplestore::StaticSampleStore,
};

/// AES-GCM nonce length in bytes (the only supported size).
const AES_GCM_NONCE_LEN: usize = 12;

/// AES-GCM tag length in bytes.
const AES_GCM_TAG_LEN: usize = 16;

/// Encrypts `request.plaintext` using `bssl_crypto`'s AEAD API,
/// returning separate ciphertext and authentication tag fields.
///
/// The AEAD algorithm is chosen based on the key length:
/// - 16 bytes → AES-128-GCM
/// - 32 bytes → AES-256-GCM
fn encrypt(
    request: service::oak::crypto_test::AeadEncryptRequest,
) -> Result<service::oak::crypto_test::AeadEncryptResponse, micro_rpc::Status> {
    let nonce: &[u8; AES_GCM_NONCE_LEN] =
        request.nonce.as_slice().try_into().map_err(|_| {
            unimplemented(format!("unsupported nonce length: {}", request.nonce.len()))
        })?;

    let sealed = match request.key.len() {
        16 => {
            let key: &[u8; 16] = request.key.as_slice().try_into().unwrap();
            Aes128Gcm::new(key).seal(nonce, &request.plaintext, &request.aad)
        }
        32 => {
            let key: &[u8; 32] = request.key.as_slice().try_into().unwrap();
            Aes256Gcm::new(key).seal(nonce, &request.plaintext, &request.aad)
        }
        len => {
            return Err(unimplemented(format!("unsupported key length: {len}")));
        }
    };

    // `seal` returns ciphertext || tag concatenated.
    let ct_len = sealed.len() - AES_GCM_TAG_LEN;
    let ciphertext = sealed[..ct_len].to_vec();
    let tag = sealed[ct_len..].to_vec();

    Ok(service::oak::crypto_test::AeadEncryptResponse { ciphertext, tag })
}

/// Decrypts `request.ciphertext` using `bssl_crypto`'s AEAD API,
/// returning the plaintext.
///
/// The AEAD algorithm is chosen based on the key length:
/// - 16 bytes → AES-128-GCM
/// - 32 bytes → AES-256-GCM
fn decrypt(
    request: service::oak::crypto_test::AeadDecryptRequest,
) -> Result<service::oak::crypto_test::AeadDecryptResponse, micro_rpc::Status> {
    let nonce: &[u8; AES_GCM_NONCE_LEN] =
        request.nonce.as_slice().try_into().map_err(|_| {
            unimplemented(format!("unsupported nonce length: {}", request.nonce.len()))
        })?;

    // `open` expects ciphertext || tag concatenated.
    let mut sealed = request.ciphertext;
    sealed.extend_from_slice(&request.tag);

    let plaintext = match request.key.len() {
        16 => {
            let key: &[u8; 16] = request.key.as_slice().try_into().unwrap();
            Aes128Gcm::new(key).open(nonce, &sealed, &request.aad)
        }
        32 => {
            let key: &[u8; 32] = request.key.as_slice().try_into().unwrap();
            Aes256Gcm::new(key).open(nonce, &sealed, &request.aad)
        }
        len => {
            return Err(unimplemented(format!("unsupported key length: {len}")));
        }
    };

    let plaintext = plaintext.ok_or_else(|| {
        micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::Internal,
            "decryption produced an error",
        )
    })?;

    Ok(service::oak::crypto_test::AeadDecryptResponse { plaintext })
}

/// Returns an `Unimplemented` error for unsupported parameter sizes.
fn unimplemented(message: alloc::string::String) -> micro_rpc::Status {
    micro_rpc::Status::new_with_message(micro_rpc::StatusCode::Unimplemented, message)
}

/// Service implementation that dispatches to AES-128-GCM or AES-256-GCM
/// via BoringSSL depending on the key length.
struct AeadService;

impl service::oak::crypto_test::Aead for AeadService {
    fn encrypt(
        &mut self,
        request: service::oak::crypto_test::AeadEncryptRequest,
    ) -> Result<service::oak::crypto_test::AeadEncryptResponse, micro_rpc::Status> {
        encrypt(request)
    }

    fn decrypt(
        &mut self,
        request: service::oak::crypto_test::AeadDecryptRequest,
    ) -> Result<service::oak::crypto_test::AeadDecryptResponse, micro_rpc::Status> {
        decrypt(request)
    }
}

#[entrypoint]
fn start_aead_server() -> ! {
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();
    let service = AeadService;
    let server = service::oak::crypto_test::AeadServer::new(service);
    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}
