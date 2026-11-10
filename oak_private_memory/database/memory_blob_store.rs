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

use std::collections::BTreeMap;

use ::encryption::{decrypt, encrypt, generate_nonce};
use anyhow::Context;
use external_db_client::{BlobId, DataBlobHandler, ExternalDbClient};
use log::warn;
use prost::Message;
use prost_types::Timestamp;
use sealed_memory_rust_proto::prelude::v1::*;
use zeroize::Zeroizing;

#[derive(Debug)]
pub struct ReencryptedMemories {
    /// New blob ID for each source blob, or `None` if the source blob is
    /// missing.
    pub new_blob_ids: Vec<Option<BlobId>>,
    pub ciphertext_bytes: u64,
}

/// Handles encrypting, decrypting, and storing Memory objects in the external
/// database. Each memory is serialized, encrypted with AES-GCM using the
/// session DEK, and stored as a blob.
pub(crate) struct MemoryBlobStore {
    db_client: ExternalDbClient,
    dek: Zeroizing<Vec<u8>>,
}

impl MemoryBlobStore {
    pub fn new(db_client: ExternalDbClient, dek: Zeroizing<Vec<u8>>) -> Self {
        Self { db_client, dek }
    }

    pub fn set_dek(&mut self, new_dek: Zeroizing<Vec<u8>>) {
        self.dek = new_dek;
    }

    /// Copies `blob_ids` into new blobs encrypted under `new_dek`, preserving
    /// each memory's coarsened TTL. Missing source blobs return `None`; partial
    /// writes are soft-deleted on failure.
    pub async fn reencrypt_memories(
        &self,
        blob_ids: &[BlobId],
        new_dek: &[u8],
    ) -> anyhow::Result<ReencryptedMemories> {
        let memories = self.get_memories_allowing_missing(blob_ids).await?;

        let mut new_blob_ids = Vec::with_capacity(memories.len());
        let mut ciphertext_bytes = 0;
        // Group by coarsened expiration since WriteDataBlobs takes one TTL per batch.
        let mut by_expiration: BTreeMap<(i64, i32), (Timestamp, Vec<DataBlob>)> = BTreeMap::new();
        for memory in &memories {
            let Some(memory) = memory else {
                new_blob_ids.push(None);
                continue;
            };
            let expiration_timestamp = memory
                .expiration_timestamp
                .ok_or_else(|| anyhow::anyhow!("missing expiration_timestamp in memory"))?;
            let (blob_id, data_blob) = Self::encrypt_memory_blob(new_dek, memory)?;
            let expiration = crate::clock::round_up_to_daily_boundary(expiration_timestamp);
            ciphertext_bytes += data_blob.blob.len() as u64;
            by_expiration
                .entry((expiration.seconds, expiration.nanos))
                .or_insert_with(|| (expiration, Vec::new()))
                .1
                .push(data_blob);
            new_blob_ids.push(Some(blob_id));
        }

        let mut db_client = self.db_client.clone();
        let mut written: Vec<BlobId> = Vec::with_capacity(new_blob_ids.len());
        for (expiration, data_blobs) in by_expiration.into_values() {
            let ids: Vec<BlobId> =
                data_blobs.iter().map(|data_blob| data_blob.id.clone()).collect();
            if let Err(e) = db_client.add_blobs(data_blobs, expiration).await {
                if !written.is_empty()
                    && let Err(delete_error) =
                        DataBlobHandler::delete_blobs(&mut db_client, &written).await
                {
                    warn!(
                        "Failed to soft-delete {} partial copies: {delete_error:?}",
                        written.len()
                    );
                }
                return Err(e);
            }
            written.extend(ids);
        }
        Ok(ReencryptedMemories { new_blob_ids, ciphertext_bytes })
    }

    /// Reads and decrypts `blob_ids`, returning `None` for blobs that no longer
    /// exist instead of failing.
    ///
    /// A blob can be missing while the index still references it, e.g. when
    /// the TTL sweeper removed an expired memory's blob before the session
    /// purged the memory. That is permanent, so it must not fail the caller:
    /// re-encryption skips the memory instead.
    ///
    /// The host fails the whole `ReadDataBlobs` batch with `NOT_FOUND` if any
    /// blob is missing. Only then does this fall back to reading the blobs
    /// one by one, mapping a missing blob to `None`. Any other batch error
    /// (e.g. `UNAVAILABLE`, `DEADLINE_EXCEEDED`) is returned as is so the
    /// client can retry. Errors from the single reads, blobs that fail to
    /// decrypt, and blobs that fail to decode are returned too.
    async fn get_memories_allowing_missing(
        &self,
        blob_ids: &[BlobId],
    ) -> anyhow::Result<Vec<Option<Memory>>> {
        let encrypted_blobs = match self.db_client.clone().get_blobs(blob_ids).await {
            Ok(blobs) => blobs,
            Err(e)
                if e.downcast_ref::<tonic::Status>()
                    .is_some_and(|status| status.code() == tonic::Code::NotFound) =>
            {
                warn!(
                    "batch read of {} blobs hit a missing blob, reading one by one",
                    blob_ids.len()
                );
                let mut blobs = Vec::with_capacity(blob_ids.len());
                for blob_id in blob_ids {
                    blobs.push(self.db_client.clone().get_blob(blob_id).await?);
                }
                blobs
            }
            Err(e) => return Err(e),
        };
        blob_ids
            .iter()
            .zip(encrypted_blobs)
            .map(|(blob_id, encrypted_blob)| {
                let Some(encrypted_blob) = encrypted_blob else {
                    warn!("blob {blob_id} not found; it will not be re-encrypted");
                    return Ok(None);
                };
                let decrypted_data = self
                    .decrypt_blob(blob_id, &encrypted_blob)
                    .with_context(|| format!("decrypting blob {blob_id}"))?;
                Ok(Some(Memory::decode(&*decrypted_data)?))
            })
            .collect()
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
        dek: &[u8],
        memory: &Memory,
        blob_id: &BlobId,
    ) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
        let memory_data = memory.encode_to_vec();
        let nonce = generate_nonce();
        let encrypted_data = encrypt(dek, &nonce, &memory_data, blob_id.as_bytes())?;
        Ok((encrypted_data, nonce))
    }

    fn encrypt_memory_blob(dek: &[u8], memory: &Memory) -> anyhow::Result<(BlobId, DataBlob)> {
        let blob_id: BlobId = rand::random::<u128>().to_string();
        let (encrypted_data, nonce) = Self::encode_encrypt_memory(dek, memory, &blob_id)?;
        let encrypted_blob = EncryptedDataBlob { nonce, data: encrypted_data };
        let data_blob = DataBlob { id: blob_id.clone(), blob: encrypted_blob.encode_to_vec() };
        Ok((blob_id, data_blob))
    }

    /// Encrypts a memory and builds a DataBlob ready for storage.
    /// Returns (blob_id, data_blob, expiration_timestamp).
    fn prepare_blob(&self, memory: &Memory) -> anyhow::Result<(BlobId, DataBlob, Timestamp)> {
        let expiration_timestamp = memory
            .expiration_timestamp
            .ok_or_else(|| anyhow::anyhow!("missing expiration_timestamp in memory"))?;
        let (blob_id, data_blob) = Self::encrypt_memory_blob(&self.dek, memory)?;
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use private_memory_test_database_server_lib::service::{
        self, SealedMemoryDatabaseServiceTestImpl,
    };
    use tokio::net::TcpListener;
    use tonic::transport::Channel;

    use super::*;

    const DAY: i64 = 24 * 60 * 60;

    async fn start_fake() -> (ExternalDbClient, Arc<SealedMemoryDatabaseServiceTestImpl>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let fake = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
        tokio::spawn(service::serve(listener, fake.clone()));
        let channel =
            Channel::from_shared(format!("http://{addr}")).unwrap().connect().await.unwrap();
        (ExternalDbClient::new(channel), fake)
    }

    fn memory(id: &str, expiration_seconds: Option<i64>) -> Memory {
        Memory {
            id: id.to_string(),
            tags: vec![format!("tag-{id}")],
            expiration_timestamp: expiration_seconds.map(|seconds| Timestamp { seconds, nanos: 0 }),
            ..Default::default()
        }
    }

    fn coarsened(seconds: i64) -> Timestamp {
        crate::clock::round_up_to_daily_boundary(Timestamp { seconds, nanos: 0 })
    }

    async fn store(store: &MemoryBlobStore, memory: &Memory) -> BlobId {
        let (blob_id, data_blob) =
            MemoryBlobStore::encrypt_memory_blob(&store.dek, memory).unwrap();
        store.db_client.clone().add_blobs(vec![data_blob], coarsened(1000 * DAY)).await.unwrap();
        blob_id
    }

    #[tokio::test]
    async fn reencrypt_keeps_order_and_each_memorys_own_ttl() {
        let (client, fake) = start_fake().await;
        let old_store = MemoryBlobStore::new(client.clone(), Zeroizing::new(vec![1u8; 32]));
        let memories = [
            memory("short", Some(10 * DAY + 5)),
            memory("long", Some(400 * DAY + 5)),
            memory("short-too", Some(10 * DAY + 7)),
        ];
        let mut old_ids = Vec::new();
        for memory in &memories {
            old_ids.push(store(&old_store, memory).await);
        }

        let new_dek = Zeroizing::new(vec![2u8; 32]);
        let result = old_store.reencrypt_memories(&old_ids, &new_dek).await.unwrap();

        let new_ids: Vec<BlobId> = result.new_blob_ids.into_iter().map(Option::unwrap).collect();
        let new_store = MemoryBlobStore::new(client, new_dek);
        assert_eq!(new_store.get_memories_by_blob_ids(&new_ids).await.unwrap(), memories);
        let expirations = fake.blob_expirations.lock().await;
        assert_eq!(expirations[&new_ids[0]], coarsened(10 * DAY + 5));
        assert_eq!(expirations[&new_ids[1]], coarsened(400 * DAY + 5));
        assert_eq!(expirations[&new_ids[2]], coarsened(10 * DAY + 7));
        let db = fake.database.lock().await;
        let written: u64 = new_ids.iter().map(|id| db[id].blob.len() as u64).sum();
        assert_eq!(result.ciphertext_bytes, written);
        drop(db);
        assert_eq!(old_store.get_memories_by_blob_ids(&old_ids).await.unwrap(), memories);
    }

    #[tokio::test]
    async fn reencrypt_reports_missing_blobs_and_copies_the_rest() {
        let (client, fake) = start_fake().await;
        let old_store = MemoryBlobStore::new(client.clone(), Zeroizing::new(vec![1u8; 32]));
        let kept = memory("kept", Some(10 * DAY));
        let kept_id = store(&old_store, &kept).await;
        let gone_id = store(&old_store, &memory("gone", Some(10 * DAY))).await;
        fake.database.lock().await.remove(&gone_id);

        let new_dek = Zeroizing::new(vec![2u8; 32]);
        let result = old_store.reencrypt_memories(&[gone_id, kept_id], &new_dek).await.unwrap();

        assert_eq!(result.new_blob_ids[0], None);
        let new_id = result.new_blob_ids[1].clone().unwrap();
        let new_store = MemoryBlobStore::new(client, new_dek);
        assert_eq!(new_store.get_memory_by_blob_id(&new_id).await.unwrap(), kept);
    }

    #[tokio::test]
    async fn reencrypt_returns_other_batch_read_errors_without_reading_one_by_one() {
        let (client, fake) = start_fake().await;
        let old_store = MemoryBlobStore::new(client, Zeroizing::new(vec![1u8; 32]));
        let blob_id = store(&old_store, &memory("kept", Some(10 * DAY))).await;
        fake.fail_next_read_data_blobs.store(true, std::sync::atomic::Ordering::SeqCst);

        let error = old_store.reencrypt_memories(&[blob_id], &[2u8; 32]).await.unwrap_err();

        let status = error.downcast_ref::<tonic::Status>().expect("expected a tonic::Status");
        assert_eq!(status.code(), tonic::Code::Unavailable);
    }

    #[tokio::test]
    async fn reencrypt_rejects_memory_without_expiration() {
        let (client, _) = start_fake().await;
        let old_store = MemoryBlobStore::new(client, Zeroizing::new(vec![1u8; 32]));
        let no_ttl_id = store(&old_store, &memory("no_ttl", None)).await;

        let result = old_store.reencrypt_memories(&[no_ttl_id], &[2u8; 32]).await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn reencrypt_fails_on_undecryptable_blob_and_writes_nothing() {
        let (client, fake) = start_fake().await;
        let other_store = MemoryBlobStore::new(client.clone(), Zeroizing::new(vec![9u8; 32]));
        let foreign_id = store(&other_store, &memory("foreign", Some(10 * DAY))).await;
        let old_store = MemoryBlobStore::new(client, Zeroizing::new(vec![1u8; 32]));

        let error = old_store
            .reencrypt_memories(std::slice::from_ref(&foreign_id), &[2u8; 32])
            .await
            .unwrap_err();

        assert!(error.downcast_ref::<tonic::Status>().is_none(), "{error:#}");
        assert!(
            format!("{error:#}").contains(&format!("decrypting blob {foreign_id}")),
            "{error:#}"
        );
        let blob_ids: Vec<String> = fake.database.lock().await.keys().cloned().collect();
        assert_eq!(blob_ids, vec![foreign_id]);
    }
}
