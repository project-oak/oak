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

use aes_gcm_siv::{
    Aes256GcmSiv, Key, Nonce,
    aead::{Aead, AeadCore, KeyInit, OsRng},
};
use anyhow::{Error, anyhow};

pub fn generate_nonce() -> Vec<u8> {
    Aes256GcmSiv::generate_nonce(&mut OsRng).to_vec()
}

pub fn encrypt(key: &[u8], nonce: &[u8], message: &[u8]) -> Result<Vec<u8>, Error> {
    let key = Key::<Aes256GcmSiv>::from_slice(key);
    let cipher = Aes256GcmSiv::new(key);
    cipher.encrypt(Nonce::from_slice(nonce), message).map_err(|x| anyhow!("{}", x))
}

pub fn decrypt(key: &[u8], nonce: &[u8], message: &[u8]) -> Result<Vec<u8>, Error> {
    let key = Key::<Aes256GcmSiv>::from_slice(key);
    let cipher = Aes256GcmSiv::new(key);
    cipher.decrypt(Nonce::from_slice(nonce), message).map_err(|x| anyhow!("{}", x))
}
