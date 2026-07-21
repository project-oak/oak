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

//! Enclave application that exposes AES-GCM AEAD operations via micro_rpc.
//!
//! This binary runs under the Oak Restricted Kernel and implements the
//! [`service::oak::crypto_test::Crypto`] service using the `aes-gcm` crate.
//! It is used by the integration test to exercise the crypto implementation
//! against Wycheproof test vectors.
//!
//! The service is intentionally kept separate from the test so that it can
//! be replaced by an alternative implementation (e.g. using a different
//! crypto library) without changing the test itself.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use alloc::{boxed::Box, format, string::ToString};

use aes_gcm::{AeadInPlace, Aes128Gcm, Aes256Gcm, KeyInit, Nonce, Tag};
use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, start_blocking_server},
    entrypoint,
    utils::samplestore::StaticSampleStore,
};
use service::oak::crypto_test::{
    AeadDecryptRequest, AeadDecryptResponse, AeadEncryptRequest, AeadEncryptResponse, Crypto,
    MlKemDecapsulateFromSeedRequest, MlKemDecapsulateResponse, MlKemKeyGenRequest,
    MlKemKeyGenResponse,
};

/// Encrypts the plaintext from `request` in-place using the given AEAD
/// cipher type, returning the ciphertext and authentication tag.
fn encrypt_aead<C: KeyInit + AeadInPlace>(
    request: AeadEncryptRequest,
) -> Result<AeadEncryptResponse, micro_rpc::Status> {
    let cipher = C::new_from_slice(&request.key).map_err(|e| {
        micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::InvalidArgument,
            format!("invalid key: {e}"),
        )
    })?;
    let nonce_len = request.nonce.len();
    let nonce = Nonce::from_exact_iter(request.nonce)
        .ok_or_else(|| unimplemented(format!("unsupported nonce length: {nonce_len}")))?;
    let mut ciphertext = request.plaintext;
    let tag =
        cipher.encrypt_in_place_detached(&nonce, &request.aad, &mut ciphertext).map_err(|e| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("encryption failed: {e}"),
            )
        })?;
    Ok(AeadEncryptResponse { ciphertext, tag: tag.to_vec() })
}

/// Decrypts the ciphertext from `request` in-place using the given AEAD
/// cipher type, returning the plaintext.
fn decrypt_aead<C: KeyInit + AeadInPlace>(
    request: AeadDecryptRequest,
) -> Result<AeadDecryptResponse, micro_rpc::Status> {
    let cipher = C::new_from_slice(&request.key).map_err(|e| {
        micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::InvalidArgument,
            format!("invalid key: {e}"),
        )
    })?;
    let nonce_len = request.nonce.len();
    let nonce = Nonce::from_exact_iter(request.nonce)
        .ok_or_else(|| unimplemented(format!("unsupported nonce length: {nonce_len}")))?;
    let tag_len = request.tag.len();
    let tag = Tag::from_exact_iter(request.tag).ok_or_else(|| {
        micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::InvalidArgument,
            format!("invalid tag length: {tag_len}"),
        )
    })?;
    let mut plaintext = request.ciphertext;
    cipher.decrypt_in_place_detached(&nonce, &request.aad, &mut plaintext, &tag).map_err(|e| {
        micro_rpc::Status::new_with_message(
            micro_rpc::StatusCode::Internal,
            format!("decryption failed: {e}"),
        )
    })?;
    Ok(AeadDecryptResponse { plaintext })
}

/// Returns an `Unimplemented` error for unsupported parameter sizes.
fn unimplemented(message: alloc::string::String) -> micro_rpc::Status {
    micro_rpc::Status::new_with_message(micro_rpc::StatusCode::Unimplemented, message)
}

/// Message returned for every (unsupported) ML-KEM operation.
const ML_KEM_UNSUPPORTED: &str = "ML-KEM is not supported by the aes-gcm enclave app";

/// `aes-gcm`-backed implementation of the [`Crypto`] service.
///
/// AEAD dispatches to AES-128-GCM or AES-256-GCM depending on the key length.
/// The `aes-gcm` crate has no post-quantum primitives, so all ML-KEM operations
/// return `Unimplemented`. This still lets the same integration test run
/// against this enclave: ML-KEM vectors are simply recorded as unsupported
/// (skipped).
struct CryptoService;

impl Crypto for CryptoService {
    fn encrypt(
        &mut self,
        request: AeadEncryptRequest,
    ) -> Result<AeadEncryptResponse, micro_rpc::Status> {
        match request.key.len() {
            16 => encrypt_aead::<Aes128Gcm>(request),
            32 => encrypt_aead::<Aes256Gcm>(request),
            len => Err(unimplemented(format!("unsupported key length: {len}"))),
        }
    }

    fn decrypt(
        &mut self,
        request: AeadDecryptRequest,
    ) -> Result<AeadDecryptResponse, micro_rpc::Status> {
        match request.key.len() {
            16 => decrypt_aead::<Aes128Gcm>(request),
            32 => decrypt_aead::<Aes256Gcm>(request),
            len => Err(unimplemented(format!("unsupported key length: {len}"))),
        }
    }

    fn key_gen(
        &mut self,
        _request: MlKemKeyGenRequest,
    ) -> Result<MlKemKeyGenResponse, micro_rpc::Status> {
        Err(unimplemented(ML_KEM_UNSUPPORTED.to_string()))
    }

    fn decapsulate_from_seed(
        &mut self,
        _request: MlKemDecapsulateFromSeedRequest,
    ) -> Result<MlKemDecapsulateResponse, micro_rpc::Status> {
        Err(unimplemented(ML_KEM_UNSUPPORTED.to_string()))
    }
}

#[entrypoint]
fn start_crypto_server() -> ! {
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();
    let server = service::oak::crypto_test::CryptoServer::new(CryptoService);
    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}
