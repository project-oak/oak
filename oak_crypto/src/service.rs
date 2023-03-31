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

use crate::{
    encryptor::{
        CryptoContext, CryptoContextGenerator, OAK_HPKE_INFO, TEST_ENCAPSULATED_PUBLIC_KEY,
    },
    hpke::{setup_base_recipient, KeyPair},
};
use alloc::vec::Vec;
use anyhow::Context;

pub struct EnclaveEncryptionKeyProvider {
    // TODO(#3841): Move the corresponding key pair to the kernel and provide a micro RPC API.
    key_pair: KeyPair,
}

impl Default for EnclaveEncryptionKeyProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl EnclaveEncryptionKeyProvider {
    pub fn new() -> Self {
        Self {
            key_pair: KeyPair::generate(),
        }
    }

    /// Returns a NIST P-256 SEC1 encoded point public key.
    /// <https://secg.org/sec1-v2.pdf>
    pub fn get_serialized_public_key(&self) -> Vec<u8> {
        self.key_pair.get_serialized_public_key()
    }
}

impl CryptoContextGenerator for EnclaveEncryptionKeyProvider {
    fn generate_context(&self) -> anyhow::Result<CryptoContext> {
        let (recipient_request_context, recipient_response_context) =
            setup_base_recipient(&TEST_ENCAPSULATED_PUBLIC_KEY, &self.key_pair, OAK_HPKE_INFO)
                .context("couldn't generate recipient crypto context")?;
        Ok(CryptoContext {
            recipient_request_context,
            recipient_response_context,
        })
    }
}
