//
// Copyright 2023 The Project Oak Authors
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

//! Interface and implementation of the asymmetric identity key to be used in
//! the authentication schemes.

use alloc::vec::Vec;

use anyhow::anyhow;

use crate::noise_handshake::{P256Scalar, client::P256_SCALAR_LEN, p256_scalar_mult};

pub trait IdentityKeyHandle: Send {
    fn get_public_key(&self) -> anyhow::Result<Vec<u8>>;
    fn derive_dh_secret(&self, peer_public_key: &[u8]) -> anyhow::Result<Vec<u8>>;
}

// Implementation of the identity keyset where the private key is encapsulated
// and the cryptographic operations are performed in process.
pub struct IdentityKey {
    private_key: P256Scalar,
}

impl IdentityKey {
    pub fn generate() -> Self {
        Self { private_key: P256Scalar::generate() }
    }

    pub fn from_bytes(bytes: [u8; P256_SCALAR_LEN]) -> Self {
        Self { private_key: P256Scalar::from_bytes(bytes) }
    }
}

impl IdentityKeyHandle for IdentityKey {
    fn get_public_key(&self) -> anyhow::Result<Vec<u8>> {
        Ok(self.private_key.compute_public_key().to_vec())
    }

    fn derive_dh_secret(&self, peer_public_key: &[u8]) -> anyhow::Result<Vec<u8>> {
        p256_scalar_mult(
            &self.private_key,
            peer_public_key
                .try_into()
                .map_err(|error| anyhow!("invalid peer public key: {:?}", error))?,
        )
        .map_err(|error| anyhow!("error deriving the DH secret: {error:?}"))
        .map(|s| s.to_vec())
    }
}
