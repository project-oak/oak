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

use ::encryption::{decrypt, encrypt, generate_nonce};
use anyhow::Context;
use external_db_client::{BlobId, DataBlobHandler, ExternalDbClient};
use prost::Message;
use sealed_memory_rust_proto::prelude::v1::*;

/// Handles encrypting, decrypting, and storing Memory objects in the external
/// database. Each memory is serialized, encrypted with AES-GCM using the
/// session DEK, and stored as a blob.
pub(crate) struct MemoryBlobStore {
    db_client: ExternalDbClient,
    dek: Vec<u8>,
}

impl MemoryBlobStore {
    pub fn new(db_client: ExternalDbClient, dek: Vec<u8>) -> Self {
        Self { db_client, dek }
    }

    async fn fetch_decrypt_decode_memory(&self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        let encrypted_blob = self
            .db_client
            .clone()
            .get_blob(blob_id, false)
            .await?
            .context(format!("blob not found for id: {}", blob_id))?;
        let decrypted_data = decrypt(&self.dek, &encrypted_blob.nonce, &encrypted_blob.data)?;
        Ok(Memory::decode(&*decrypted_data)?)
    }

    pub async fn get_memory_by_blob_id(&mut self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        self.fetch_decrypt_decode_memory(blob_id).await
    }

    pub async fn get_memories_by_blob_ids(
        &mut self,
        blob_ids: &[BlobId],
    ) -> anyhow::Result<Vec<Memory>> {
        let encrypted_blobs = self.db_client.get_blobs(blob_ids, false).await?;
        blob_ids
            .iter()
            .zip(encrypted_blobs)
            .map(|(blob_id, encrypted_blob_opt)| {
                let encrypted_blob = encrypted_blob_opt
                    .ok_or_else(|| anyhow::anyhow!("blob not found for id: {}", blob_id))?;
                let decrypted_data =
                    decrypt(&self.dek, &encrypted_blob.nonce, &encrypted_blob.data)?;
                Ok(Memory::decode(&*decrypted_data)?)
            })
            .collect()
    }

    /// Encodes and encrypts a memory, returning the blob and a generated nonce.
    fn encode_encrypt_memory(&self, memory: &Memory) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let memory_data = memory.encode_to_vec();
        let nonce = generate_nonce();
        let encrypted_data = encrypt(&self.dek, &nonce, &memory_data)?;
        Ok((encrypted_data, nonce))
    }

    pub async fn add_memory(&mut self, memory: &Memory) -> anyhow::Result<BlobId> {
        let blob_id: BlobId = rand::random::<u128>().to_string();
        let (encrypted_data, nonce) = self.encode_encrypt_memory(memory)?;
        let encrypted_blob = EncryptedDataBlob { nonce, data: encrypted_data };

        // Store in external DB, explicitly providing the generated ID
        self.db_client.add_blob(encrypted_blob, Some(blob_id.clone())).await?;

        Ok(blob_id)
    }

    pub async fn delete_memories(&mut self, blob_ids: &[BlobId]) -> anyhow::Result<()> {
        DataBlobHandler::delete_blobs(&mut self.db_client, blob_ids).await?;
        Ok(())
    }
}
