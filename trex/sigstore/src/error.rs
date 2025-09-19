//
// Copyright 2025 The Project Oak Authors
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

//! General error type for the sigstore crate.

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("Base64 decode error: {0}")]
    Base64(#[from] base64::DecodeError),
    #[error("Hex decode error: {0}")]
    Hex(#[from] hex::FromHexError),
    #[error("Signature DER decode error: {0:?}")]
    SignatureDer(p256::ecdsa::Error),
    #[error("Signature verification failed: {0:?}")]
    SignatureVerification(p256::ecdsa::Error),
    #[error("Could not decode public key: {0:?}")]
    PublicKeyDecode(p256::pkcs8::spki::Error),
    #[error("Could not convert public key from bytes: {0}")]
    PublicKeyBytes(#[from] core::str::Utf8Error),
    #[error("Error while decoding public key from PEM: {0:?}")]
    PublicKeyPem(p256::pkcs8::Error),
}
