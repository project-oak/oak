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

use anyhow::Context;
use encryption::{decrypt, encrypt, generate_nonce};
use log::error;
use prost::Message;
use sealed_memory_rust_proto::prelude::v1::*;

/// Helpers for encryption/decryting the database blobs.
pub fn encrypt_database(
    database: &EncryptedUserInfo,
    key: &[u8],
) -> anyhow::Result<EncryptedDataBlob> {
    let nonce = generate_nonce();
    let datablob = database.encode_to_vec();
    let data = encrypt(key, &nonce, &datablob)?;
    Ok(EncryptedDataBlob { nonce, data })
}

pub fn decrypt_database(
    datablob: EncryptedDataBlob,
    key: &[u8],
) -> anyhow::Result<EncryptedUserInfo> {
    let nonce = datablob.nonce;
    let data = datablob.data;
    let decrypted_data = match decrypt(key, &nonce, &data) {
        Ok(data) => data,
        Err(err) => {
            error!(
                "Failed to decrypt database: key_len={}, nonce_len={}, data_len={}, error={:?}",
                key.len(),
                nonce.len(),
                data.len(),
                err
            );
            return Err(err);
        }
    };
    let user_db = EncryptedUserInfo::decode(decrypted_data.as_slice())
        .context("Failed to decode EncryptedUserInfo")?;
    Ok(user_db)
}
