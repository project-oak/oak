//
// Copyright 2022 The Project Oak Authors
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

use anyhow::Context;
use tink_core::keyset::Handle;
use tink_hybrid::init;

pub trait CryptoEngine {
    fn encrypt(&self, plaintext_message: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn decrypt(&self, encrypted_message: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// Context info value for encryption and decryption.
/// 
/// The value should be the same for both encryption and decryption to ensure
/// the correct decryption of a ciphertext:
/// https://docs.rs/tink-core/0.2.4/tink_core/trait.HybridDecrypt.html#security-guarantees
pub const HYBRID_ENCRYPTION_CONTEXT_INFO: &[u8] = b"Oak Non-Interactive Attestation v0.1";

pub struct ClientEncryptor {
    enclave_public_key: &Handle,
}

impl ClientEncryptor {
    pub fn new(enclave_public_key: &[u8]) -> Self {
        Self {}
    }

    pub fn encrypt(&self, plaintext_message: &[u8]) -> anyhow::Result<(Vec<u8>, ClientDecryptor)> {
        let encryptor = tink_hybrid::new_encrypt(self.enclave_public_key)
            .map_err(|error| anyhow!("couldn't create hybrid encryptor: {}", error))?;
        let encrypted_message = encryptor
            .encrypt(plaintext_message, HYBRID_ENCRYPTION_CONTEXT_INFO)
            .map_err(|error| anyhow!("couldn't encrypt data: {}", error))?;
    }
}

pub struct ClientDecryptor {
    fn decrypt(&self, encrypted_message: &[u8]) -> anyhow::Result<Vec<u8>>;
}

pub struct ServerHybridCryptoEngineBuilder {

}

fn main() {
    let client_encryptor = ClientEncryptor::new(enclave_public_key);
    let encrypted_message = 
}
