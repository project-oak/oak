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

use anyhow::{anyhow, Context, Error};
use oak_crypto::{
    encryptor::{Encryptor, Payload},
    noise_handshake::{OrderedCrypter, UnorderedCrypter, NONCE_LEN},
};

// This is the default implementation of the encryptor to use for the Noise
// protocol (consecutive nonces, no packet drop or reordering allowed)
pub struct OrderedChannelEncryptor {
    crypter: OrderedCrypter,
}

impl Encryptor for OrderedChannelEncryptor {
    fn encrypt(&mut self, plaintext: Payload) -> anyhow::Result<Payload> {
        self.crypter
            .encrypt(plaintext.message.as_slice())
            .map(From::from)
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }

    fn decrypt(&mut self, ciphertext: Payload) -> anyhow::Result<Payload> {
        self.crypter
            .decrypt(ciphertext.message.as_slice())
            .map(From::from)
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }
}

impl TryFrom<OrderedCrypter> for OrderedChannelEncryptor {
    type Error = anyhow::Error;

    fn try_from(crypter: OrderedCrypter) -> Result<Self, Self::Error> {
        Ok(Self { crypter })
    }
}

/// `OrderedChannelEncryptor` that explicitly ignores message ordering.
///
/// It ignores message ordering but protects against replayed messages. This
/// implementation ratchets messages upto a given `window_size` i.e. very old
/// messages outside the given window will fail decryption. Messages within the
/// allowed window will be decrypted in any order. Applications using this
/// implementation must ensure they can handle re-ordered and dropped messages.
pub struct UnorderedChannelEncryptor {
    pub crypter: UnorderedCrypter,
}

impl Encryptor for UnorderedChannelEncryptor {
    fn encrypt(&mut self, plaintext: Payload) -> anyhow::Result<Payload> {
        self.crypter
            .encrypt(plaintext.message.as_slice())
            .map(From::from)
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }

    fn decrypt(&mut self, ciphertext: Payload) -> anyhow::Result<Payload> {
        let nonce: [u8; NONCE_LEN] = ciphertext
            .nonce
            .as_ref()
            .context("payload is missing nonce")?
            .clone()
            .try_into()
            .map_err(|e| anyhow!("Failed to extract nonce error: {e:#?}"))?;
        self.crypter
            .decrypt(&nonce, ciphertext.message.as_slice())
            .map(From::from)
            .map_err(|e| anyhow!("Encryption error: {e:#?}"))
    }
}

impl TryFrom<(OrderedCrypter, u32)> for UnorderedChannelEncryptor {
    type Error = anyhow::Error;

    fn try_from(sk_and_window_size: (OrderedCrypter, u32)) -> Result<Self, Error> {
        Ok(Self {
            crypter: sk_and_window_size
                .try_into()
                .context("creating Noise crypter from the provided session keys and window size")?,
        })
    }
}
