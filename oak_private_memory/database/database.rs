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

use std::sync::Arc;

use anyhow::{Context, bail};
use external_db_client::{BlobId, ExternalDbClient};
use icing::OptimizeResultProto;
use log::info;
use prost::Message;
use prost_types::Timestamp;
use rand::Rng;
use sealed_memory_rust_proto::prelude::v1::*;

use crate::{
    IcingTempDir, MemoryId,
    clock::{Clock, SystemClock, system_time_to_timestamp},
    icing::{IcingMetaDatabase, PageToken},
    memory_blob_store::MemoryBlobStore,
};

// Maximum size of the database (metadata blob). This can exceed the gRPC
// message size limit because streaming read/write is used for persistence.
pub const MAX_DATABASE_SIZE: usize = 250 * 1024 * 1024; // 250 MB

// Maximum gRPC decode size for non-streaming messages.
pub const MAX_GRPC_DECODE_SIZE: usize = 100 * 1024 * 1024; // 100 MB
/// A database that combines an Icing metadata index with encrypted blob
/// storage. It loads the metadata index at start, then fetches memory
/// contents from the external database on demand.
pub struct Database {
    database: IcingMetaDatabase,
    blob_store: MemoryBlobStore,
    key_derivation_info: KeyDerivationInfo,
    current_size: usize,
    max_size: usize,
    clock: Arc<dyn Clock>,
    blanket_ttl_seconds: i64,
}

impl Database {
    pub fn new(
        database: IcingMetaDatabase,
        dek: Vec<u8>,
        db_client: ExternalDbClient,
        key_derivation_info: KeyDerivationInfo,
        initial_size: usize,
        blanket_ttl_seconds: i64,
    ) -> Self {
        Self {
            database,
            blob_store: MemoryBlobStore::new(db_client, dek),
            key_derivation_info,
            current_size: initial_size,
            max_size: MAX_DATABASE_SIZE,
            clock: Arc::new(SystemClock),
            blanket_ttl_seconds,
        }
    }

    pub fn with_clock(mut self, clock: Arc<dyn Clock>) -> Self {
        self.clock = clock;
        self
    }

    pub fn with_max_size(mut self, max_size: usize) -> Self {
        self.max_size = max_size;
        self
    }

    pub fn max_size(&self) -> usize {
        self.max_size
    }

    pub fn meta_db(&mut self) -> &mut IcingMetaDatabase {
        &mut self.database
    }

    pub fn export(&self) -> anyhow::Result<UserDb> {
        let icing_db = self.database.export()?;
        Ok(UserDb {
            encrypted_info: Some(EncryptedUserInfo { icing_db: Some(icing_db) }),
            plaintext_info: Some(PlainTextUserInfo {
                key_derivation_info: Some(self.key_derivation_info.clone()),
                wrapped_dek: None,
            }),
        })
    }

    pub fn optimize(&mut self) -> anyhow::Result<OptimizeResultProto> {
        self.database.optimize()
    }

    /// Returns true if the cached database contains content that doesnt exist
    /// in durable storage, and should be written back.
    pub fn changed(&self) -> bool {
        self.database.needs_writeback()
    }

    /// Clear the mutation log after the database has been successfully
    /// persisted.
    pub fn mark_persisted(&mut self) {
        self.database.mark_persisted();
    }

    /// Rebases the database onto a new base blob, replaying any pending
    /// mutations. Returns the number of operations that failed to replay.
    pub fn rebase(&mut self, new_blob: &[u8]) -> anyhow::Result<usize> {
        let tempdir = IcingTempDir::new("pm-rebase");
        let (new_db, failed_operations) =
            IcingMetaDatabase::import_with_changes(tempdir, new_blob, &self.database)?;
        self.database = new_db;
        // Recalculate size after rebase
        let icing_db = self.database.export()?;
        self.current_size = icing_db.encoded_len();
        // This doesn't account for cached memories not in the new blob, but they should
        // be few.
        Ok(failed_operations)
    }

    fn add_memory_id(&mut self, memory: &mut Memory) {
        if memory.id.is_empty() {
            memory.id = rand::rng().random::<u64>().to_string();
        }
    }

    fn add_llm_view_ids(&mut self, memory: &mut Memory) {
        if let Some(views) = memory.views.as_mut() {
            for view in views.llm_views.iter_mut() {
                if view.id.is_empty() {
                    view.id = rand::rng().random::<u64>().to_string();
                }
            }
        }
    }

    fn add_created_timestamp(&mut self, memory: &mut Memory) {
        memory.created_timestamp = Some(system_time_to_timestamp(self.clock.now()));
    }

    pub fn calculate_coarsened_blanket_ttl(&self) -> Timestamp {
        crate::clock::calculate_coarsened_blanket_ttl(self.clock.as_ref(), self.blanket_ttl_seconds)
    }

    pub async fn add_memory(&mut self, mut memory: Memory) -> anyhow::Result<MemoryId> {
        self.add_memory_id(&mut memory);
        self.add_llm_view_ids(&mut memory);
        self.add_created_timestamp(&mut memory);

        let additional_size = crate::icing::calculate_memory_icing_size(&memory)?;

        if self.current_size + additional_size > self.max_size {
            bail!(
                "Database size limit exceeded: current {}, additional {}, limit {}",
                self.current_size,
                additional_size,
                self.max_size
            );
        }

        let blob_id = self.blob_store.add_memory(&memory).await?;
        self.meta_db().add_memory(&memory, blob_id)?;
        self.current_size += additional_size;
        Ok(memory.id)
    }

    pub async fn get_memories_by_tag(
        &self,
        tag: &str,
        result_mask: &Option<ResultMask>,
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(Vec<Memory>, PageToken)> {
        let (all_blob_ids, next_page_token) =
            self.database.get_memories_by_tag(tag, page_size, page_token)?;

        if all_blob_ids.is_empty() {
            return Ok((Vec::new(), PageToken::Start));
        }

        let mut memories = self.blob_store.get_memories_by_blob_ids(&all_blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, result_mask);

        Ok((memories, next_page_token))
    }

    pub async fn get_memory_by_id(
        &self,
        id: MemoryId,
        result_mask: &Option<ResultMask>,
    ) -> anyhow::Result<Option<Memory>> {
        if let Some(blob_id) = self.database.get_blob_id_by_memory_id(id.clone())? {
            self.blob_store.get_memory_by_blob_id(&blob_id).await.map(|mut m| {
                Self::apply_mask_to_memory(&mut m, result_mask);
                Some(m)
            })
        } else {
            Ok(None)
        }
    }

    /// Returns memories for the given IDs.
    /// Memories can be returned in an arbitrary order.
    /// If any memory is not found, it will be skipped and its ID collected in
    /// the second return value.
    pub async fn get_memories_by_id(
        &self,
        ids: Vec<MemoryId>,
        result_mask: &Option<ResultMask>,
    ) -> anyhow::Result<(Vec<Memory>, Vec<MemoryId>)> {
        let mut found_blob_ids: Vec<BlobId> = Vec::new();
        let mut not_found_ids: Vec<MemoryId> = Vec::new();

        for id in ids {
            match self.database.get_blob_id_by_memory_id(id.clone())? {
                Some(blob_id) => found_blob_ids.push(blob_id),
                None => not_found_ids.push(id),
            }
        }

        let mut memories = self.blob_store.get_memories_by_blob_ids(&found_blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, result_mask);

        Ok((memories, not_found_ids))
    }

    pub async fn get_memory_by_name(
        &self,
        name: &str,
        result_mask: &Option<ResultMask>,
    ) -> anyhow::Result<Option<Memory>> {
        if let Some(blob_id) = self.database.get_memory_by_name(name)? {
            self.blob_store.get_memory_by_blob_id(&blob_id).await.map(|mut m| {
                Self::apply_mask_to_memory(&mut m, result_mask);
                Some(m)
            })
        } else {
            Ok(None)
        }
    }

    pub async fn reset_memory(&mut self) -> anyhow::Result<()> {
        let all_memory_ids = self.meta_db().get_all_memory_ids()?;
        if !all_memory_ids.is_empty() {
            self.delete_memories(all_memory_ids).await?;
        }
        self.meta_db().reset()?;
        // Recalculate size based on the empty Icing DB
        let empty_icing_db = self.database.export()?;
        self.current_size = empty_icing_db.encoded_len();
        Ok(())
    }

    /// Search API v2 entry point: delegates to
    /// `IcingMetaDatabase::search_memories`.
    pub async fn search_memories(
        &self,
        request: SearchMemoriesRequest,
    ) -> anyhow::Result<(Vec<Memory>, PageToken)> {
        let (search_results, next_page_token) = self.database.search_memories(&request)?;

        if search_results.items.is_empty() {
            return Ok((Vec::new(), next_page_token));
        }

        let blob_ids: Vec<BlobId> =
            search_results.items.iter().map(|item| item.blob_id.clone()).collect();
        let mut memories = self.blob_store.get_memories_by_blob_ids(&blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, &request.result_mask);

        Ok((memories, next_page_token))
    }

    pub async fn clean_expired_memories(&mut self) -> anyhow::Result<u64> {
        let mut current_token = PageToken::Start;
        let mut num_cleaned_memories: u64 = 0;

        loop {
            let (memory_ids, next_token) =
                self.meta_db().get_expired_memories_ids(100, current_token)?;
            info!("Deleting {} expired memories.", memory_ids.len());
            self.delete_memories(memory_ids.clone()).await?;
            num_cleaned_memories += memory_ids.len() as u64;

            if next_token == PageToken::Start {
                break;
            }
            current_token = next_token;
        }

        Ok(num_cleaned_memories)
    }

    pub fn get_database_metrics(&self) -> anyhow::Result<GetDatabaseMetricsResponse> {
        let (memory_count, llm_view_count) = self.database.get_document_counts()?;
        Ok(GetDatabaseMetricsResponse {
            memory_info: Some(get_database_metrics_response::MemoryInfo {
                memory_count,
                llm_view_count,
            }),
            storage_info: Some(get_database_metrics_response::StorageInfo {
                total_storage_bytes: self.current_size as i64,
            }),
        })
    }

    pub async fn delete_memories(&mut self, ids: Vec<MemoryId>) -> anyhow::Result<()> {
        // Blob ID lookup and mutation log recording happen inside
        // IcingMetaDatabase::delete_memories. The blob IDs are stored in
        // the mutation log so they can be flushed after persistence.
        self.meta_db().delete_memories(&ids)?;
        Ok(())
    }

    /// Execute all pending blob soft-deletes against external storage.
    ///
    /// Call this **after** the Icing index has been successfully persisted.
    /// The pending deletes are derived from the Icing mutation log.
    /// Returns the number of blobs that were requested for deletion.
    pub async fn flush_pending_blob_deletes(&mut self) -> anyhow::Result<usize> {
        let blob_ids = self.database.pending_blob_deletes();
        if blob_ids.is_empty() {
            return Ok(0);
        }
        let count = blob_ids.len();
        info!("flushing {count} pending blob deletes");
        self.blob_store
            .delete_memories(&blob_ids)
            .await
            .context("flushing pending blob deletes")?;
        Ok(count)
    }

    #[allow(deprecated)]
    // Helper function to apply the result mask to a single Memory object.
    fn apply_mask_to_memory(memory: &mut Memory, mask: &Option<ResultMask>) {
        if let Some(mask) = mask {
            // include_fields is not empty, so it acts as an "only include these" list.
            if !mask.include_fields.contains(&(MemoryField::Id as i32)) {
                memory.id.clear();
            }
            if !mask.include_fields.contains(&(MemoryField::Tags as i32)) {
                memory.tags.clear();
            }
            if !mask.include_fields.contains(&(MemoryField::CreatedTimestamp as i32)) {
                memory.created_timestamp = None;
            }
            if !mask.include_fields.contains(&(MemoryField::EventTimestamp as i32)) {
                memory.event_timestamp = None;
            }
            if !mask.include_fields.contains(&(MemoryField::ExpirationTimestamp as i32)) {
                memory.expiration_timestamp = None;
            }
            if !mask.include_fields.contains(&(MemoryField::Views as i32)) {
                memory.views = None;
            }

            if !mask.include_fields.contains(&(MemoryField::Content as i32)) {
                memory.content = None;
            } else if !mask.include_content_fields.is_empty()
                && let Some(content_struct) = memory.content.as_mut()
            {
                // Filter the 'contents' map based on 'include_content_fields'.
                content_struct.contents.retain(|key, _| mask.include_content_fields.contains(key));
            }
        }
    }

    fn apply_mask_to_memories<'a>(
        memories: impl IntoIterator<Item = &'a mut Memory>,
        mask: &Option<ResultMask>,
    ) {
        if mask.is_none() {
            return;
        }

        for memory in memories.into_iter() {
            Self::apply_mask_to_memory(memory, mask)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use sealed_memory_rust_proto::{
        oak::private_memory::{LlmView, LlmViews},
        prelude::v1::{Memory, MemoryContent, MemoryField, MemoryValue, ResultMask},
    };

    use super::*;

    #[allow(deprecated)]
    fn create_memory_for_mask_test() -> Memory {
        Memory {
            id: "test_id".to_string(),
            name: String::default(),
            tags: vec!["tag1".to_string(), "tag2".to_string()],
            content: Some(MemoryContent {
                contents: HashMap::from([
                    ("key1".to_string(), MemoryValue::default()),
                    ("key2".to_string(), MemoryValue::default()),
                ]),
            }),
            created_timestamp: Some(prost_types::Timestamp::default()),
            event_timestamp: Some(prost_types::Timestamp::default()),
            expiration_timestamp: Some(prost_types::Timestamp::default()),
            views: Some(LlmViews { llm_views: vec![LlmView::default()] }),
            source: None,
        }
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_no_mask() {
        let mut memory = create_memory_for_mask_test();
        let original_memory = memory.clone();
        Database::apply_mask_to_memory(&mut memory, &None);
        assert_eq!(memory, original_memory);
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_id() {
        let mut memory = create_memory_for_mask_test();
        let mask =
            Some(ResultMask { include_fields: vec![MemoryField::Id as i32], ..Default::default() });
        Database::apply_mask_to_memory(&mut memory, &mask);
        assert_eq!(memory.id, "test_id");
        assert!(memory.tags.is_empty());
        assert!(memory.content.is_none());
        assert!(memory.created_timestamp.is_none());
        assert!(memory.event_timestamp.is_none());
        assert!(memory.expiration_timestamp.is_none());
        assert!(memory.views.is_none());
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_tags() {
        let mut memory = create_memory_for_mask_test();
        let mask = Some(ResultMask {
            include_fields: vec![MemoryField::Tags as i32],
            ..Default::default()
        });
        Database::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert_eq!(memory.tags, vec!["tag1".to_string(), "tag2".to_string()]);
        assert!(memory.content.is_none());
        assert!(memory.created_timestamp.is_none());
        assert!(memory.event_timestamp.is_none());
        assert!(memory.expiration_timestamp.is_none());
        assert!(memory.views.is_none());
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_content() {
        let mut memory = create_memory_for_mask_test();
        let mask = Some(ResultMask {
            include_fields: vec![MemoryField::Content as i32],
            include_content_fields: vec!["key1".to_string()],
        });
        Database::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert!(memory.tags.is_empty());
        assert!(memory.content.is_some());
        assert_eq!(memory.content.unwrap().contents.len(), 1);
        assert!(memory.created_timestamp.is_none());
        assert!(memory.event_timestamp.is_none());
        assert!(memory.expiration_timestamp.is_none());
        assert!(memory.views.is_none());
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_timestamps() {
        let mut memory = create_memory_for_mask_test();
        let mask = Some(ResultMask {
            include_fields: vec![
                MemoryField::CreatedTimestamp as i32,
                MemoryField::EventTimestamp as i32,
                MemoryField::ExpirationTimestamp as i32,
            ],
            ..Default::default()
        });
        Database::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert!(memory.tags.is_empty());
        assert!(memory.content.is_none());
        assert!(memory.created_timestamp.is_some());
        assert!(memory.event_timestamp.is_some());
        assert!(memory.expiration_timestamp.is_some());
        assert!(memory.views.is_none());
    }
}
