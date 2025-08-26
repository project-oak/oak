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

use std::collections::HashMap;

use anyhow::{bail, Context};
use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler, ExternalDbClient};
use prost::Message;
use sealed_memory_rust_proto::prelude::v1::*;

/// In memory cache for memories.
///
/// When a memory is added, it is cached in `MemoryCache` and also persisted at
/// disk. When a memory is fetched, if the memory is cached, it is returned
/// directly from the cached. Otherwise, it will further fetched from the
/// external storage.
/// TODO: b/412698203 - Add eviction to avoid OOM.
pub(crate) struct MemoryCache {
    db_client: ExternalDbClient,
    content_cache: HashMap<BlobId, Memory>,
    dek: Vec<u8>,
}

impl MemoryCache {
    pub fn new(db_client: ExternalDbClient, dek: Vec<u8>) -> Self {
        let content_cache = HashMap::<BlobId, Memory>::default();
        Self { db_client, dek, content_cache }
    }

    fn add_cache_entry(&mut self, blob_id: BlobId, memory: Memory) {
        const MAX_CACHE_SIZE: usize = 5;
        if self.content_cache.len() > MAX_CACHE_SIZE {
            // TODO: b/412698203 - Add eviction to avoid OOM.
            // Avoid OOM.
            self.content_cache.clear();
        }
        self.content_cache.insert(blob_id.clone(), memory);
    }

    async fn fetch_decrypt_decode_memory(&self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        let encrypted_blob = self
            .db_client
            .clone()
            .get_blob(blob_id, false)
            .await?
            .context(format!("Blob not found for id: {}", blob_id))?;
        let decrypted_data = decrypt(&self.dek, &encrypted_blob.nonce, &encrypted_blob.data)?;
        Ok(Memory::decode(&*decrypted_data)?)
    }

    pub async fn get_memory_by_blob_id(&mut self, blob_id: &BlobId) -> anyhow::Result<Memory> {
        // Check cache first
        if let Some(memory) = self.content_cache.get(blob_id) {
            return Ok(memory.clone());
        }
        // If not in cache, fetch from external DB
        let memory = self.fetch_decrypt_decode_memory(blob_id).await?;
        self.add_cache_entry(blob_id.clone(), memory.clone());
        Ok(memory)
    }

    pub async fn get_memories_by_blob_ids(
        &mut self,
        blob_ids: &[BlobId],
    ) -> anyhow::Result<Vec<Memory>> {
        let mut results: HashMap<BlobId, Memory> = HashMap::with_capacity(blob_ids.len());
        let mut missing_ids: Vec<BlobId> = Vec::new();

        // Check cache first
        for blob_id in blob_ids {
            if let Some(memory) = self.content_cache.get(blob_id) {
                results.insert(blob_id.clone(), memory.clone());
            } else {
                missing_ids.push(blob_id.clone());
            }
        }

        if !missing_ids.is_empty() {
            let encrypted_blobs = self.db_client.get_blobs(&missing_ids, false).await?;
            for (blob_id, encrypted_blob_opt) in missing_ids.iter().zip(encrypted_blobs.into_iter())
            {
                if let Some(encrypted_blob) = encrypted_blob_opt {
                    let decrypted_data =
                        decrypt(&self.dek, &encrypted_blob.nonce, &encrypted_blob.data)?;
                    let memory: Memory = Memory::decode(&*decrypted_data)?;
                    self.content_cache.insert(blob_id.clone(), memory.clone());
                    results.insert(blob_id.clone(), memory);
                } else {
                    bail!("Blob not found for id: {}", blob_id);
                }
            }
        }

        // Collect results in the original order
        blob_ids
            .iter()
            .map(|id| results.remove(id).context("id not found"))
            .collect::<anyhow::Result<Vec<_>>>()
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

        self.add_cache_entry(blob_id.clone(), memory.clone());

        Ok(blob_id)
    }

    pub async fn delete_memories(&mut self, blob_ids: &[BlobId]) -> anyhow::Result<()> {
        // Remove from local cache
        for blob_id in blob_ids {
            self.content_cache.remove(blob_id);
        }
        // Todo: Delete from external DB

        Ok(())
    }
}
