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
use log::warn;
use prost::Message;
use prost_types::Timestamp;
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

    /// Decrypts a blob, binding the blob identifier as AAD.
    ///
    /// Falls back to empty AAD for legacy blobs that were encrypted before
    /// blob-id binding was introduced. New writes always use blob-id AAD,
    /// so legacy blobs are naturally phased out via TTL expiration.
    fn decrypt_blob(&self, blob_id: &BlobId, blob: &EncryptedDataBlob) -> anyhow::Result<Vec<u8>> {
        decrypt(&self.dek, &blob.nonce, &blob.data, blob_id.as_bytes()).or_else(|_| {
            warn!(
                "blob {} failed AAD-bound decryption, retrying with empty AAD (legacy format)",
                blob_id
            );
            decrypt(&self.dek, &blob.nonce, &blob.data, b"")
        })
    }

    async fn fetch_decrypt_decode_memory(&self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        let encrypted_blob = self
            .db_client
            .clone()
            .get_blob(blob_id)
            .await?
            .context(format!("blob not found for id: {}", blob_id))?;
        let decrypted_data = self.decrypt_blob(blob_id, &encrypted_blob)?;
        Ok(Memory::decode(&*decrypted_data)?)
    }

    pub async fn get_memory_by_blob_id(&self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        self.fetch_decrypt_decode_memory(blob_id).await
    }

    pub async fn get_memories_by_blob_ids(
        &self,
        blob_ids: &[BlobId],
    ) -> anyhow::Result<Vec<Memory>> {
        let encrypted_blobs = self.db_client.clone().get_blobs(blob_ids).await?;
        blob_ids
            .iter()
            .zip(encrypted_blobs)
            .map(|(blob_id, encrypted_blob_opt)| {
                let encrypted_blob = encrypted_blob_opt
                    .ok_or_else(|| anyhow::anyhow!("blob not found for id: {}", blob_id))?;
                let decrypted_data = self.decrypt_blob(blob_id, &encrypted_blob)?;
                Ok(Memory::decode(&*decrypted_data)?)
            })
            .collect()
    }

    /// Encodes and encrypts a memory, binding the blob identifier as AAD.
    fn encode_encrypt_memory(
        &self,
        memory: &Memory,
        blob_id: &BlobId,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let memory_data = memory.encode_to_vec();
        let nonce = generate_nonce();
        let encrypted_data = encrypt(&self.dek, &nonce, &memory_data, blob_id.as_bytes())?;
        Ok((encrypted_data, nonce))
    }

    /// Encrypts a memory and builds a DataBlob ready for storage.
    /// Returns (blob_id, data_blob, expiration_timestamp).
    fn prepare_blob(&self, memory: &Memory) -> anyhow::Result<(BlobId, DataBlob, Timestamp)> {
        let blob_id: BlobId = rand::random::<u128>().to_string();
        let (encrypted_data, nonce) = self.encode_encrypt_memory(memory, &blob_id)?;
        let encrypted_blob = EncryptedDataBlob { nonce, data: encrypted_data };
        let expiration_timestamp = memory
            .expiration_timestamp
            .ok_or_else(|| anyhow::anyhow!("missing expiration_timestamp in memory"))?;
        let data_blob = DataBlob { id: blob_id.clone(), blob: encrypted_blob.encode_to_vec() };
        Ok((blob_id, data_blob, expiration_timestamp))
    }

    pub async fn add_memory(&mut self, memory: &Memory) -> anyhow::Result<BlobId> {
        let (blob_id, data_blob, expiration_timestamp) = self.prepare_blob(memory)?;
        let coarsened_expiration_timestamp =
            crate::clock::round_up_to_daily_boundary(expiration_timestamp);
        self.db_client.add_blobs(vec![data_blob], coarsened_expiration_timestamp).await?;
        Ok(blob_id)
    }

    /// Batch-add multiple memories in a single WriteDataBlobs RPC.
    /// Returns a Vec of blob_ids per memory, in order.
    pub async fn add_memories(&mut self, memories: &[&Memory]) -> anyhow::Result<Vec<BlobId>> {
        if memories.is_empty() {
            return Ok(vec![]);
        }

        let mut blob_ids = Vec::with_capacity(memories.len());
        let mut data_blobs = Vec::with_capacity(memories.len());
        let mut max_expiration: Option<Timestamp> = None;

        for memory in memories {
            let (blob_id, data_blob, expiration_timestamp) = self.prepare_blob(memory)?;

            match &max_expiration {
                Some(current_max) if expiration_timestamp.seconds > current_max.seconds => {
                    max_expiration = Some(expiration_timestamp);
                }
                None => {
                    max_expiration = Some(expiration_timestamp);
                }
                _ => {}
            }

            data_blobs.push(data_blob);
            blob_ids.push(blob_id);
        }

        let coarsened_expiration_timestamp =
            crate::clock::round_up_to_daily_boundary(max_expiration.unwrap());

        self.db_client.add_blobs(data_blobs, coarsened_expiration_timestamp).await?;

        Ok(blob_ids)
    }

    pub async fn delete_memories(&mut self, blob_ids: &[BlobId]) -> anyhow::Result<()> {
        DataBlobHandler::delete_blobs(&mut self.db_client, blob_ids).await?;
        Ok(())
    }
}
