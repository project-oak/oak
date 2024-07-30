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

//! This module provides an interface and an implementation of the Encryptor,
//! which handles encrypted communication over a channel.

use alloc::vec::Vec;

use anyhow::{anyhow, Context, Error};
use oak_crypto::{
    encryptor::{Encryptor, Payload},
    noise_handshake::Crypter,
};
use oak_proto_rust::oak::crypto::v1::SessionKeys;

// This is the default implementation of the encryptor to use for the Noise
// protocol (consecutive nonces, no packet drop or reordering allowed)
pub struct OrderedChannelEncryptor {
    crypter: Crypter,
}

impl Encryptor for OrderedChannelEncryptor {
    fn encrypt(&mut self, plaintext: Payload) -> anyhow::Result<Vec<u8>> {
        self.crypter
            .encrypt(plaintext.message.as_slice())
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }

    fn decrypt(&mut self, ciphertext: Payload) -> anyhow::Result<Vec<u8>> {
        self.crypter
            .decrypt(ciphertext.message.as_slice())
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }
}

impl TryFrom<SessionKeys> for OrderedChannelEncryptor {
    type Error = anyhow::Error;

    fn try_from(sk: SessionKeys) -> Result<Self, Error> {
        Ok(Self {
            crypter: sk
                .try_into()
                .context("error creating Noise crypter from the provided session keys")?,
        })
    }
}
