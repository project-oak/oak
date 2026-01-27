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
use external_db_client::{BlobId, ExternalDbClient};
use icing::OptimizeResultProto;
use log::info;
use rand::Rng;
use sealed_memory_rust_proto::prelude::v1::*;

use crate::{
    icing::{IcingMetaDatabase, PageToken},
    memory_cache::MemoryCache,
    IcingTempDir, MemoryId,
};

/// A database with cache. It loads the meta database of the user at start,
/// then loads documents at request. The loaded documents will be then cached
/// in memory.
pub struct DatabaseWithCache {
    database: IcingMetaDatabase,
    cache: MemoryCache,
    key_derivation_info: KeyDerivationInfo,
}

impl DatabaseWithCache {
    pub fn new(
        database: IcingMetaDatabase,
        dek: Vec<u8>,
        db_client: ExternalDbClient,
        key_derivation_info: KeyDerivationInfo,
    ) -> Self {
        Self { database, cache: MemoryCache::new(db_client, dek), key_derivation_info }
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

    /// Replace the underlying IcingMetaDatabase with a new one created from the
    /// provided blob, and then re-apply any pending changes on top of that new
    /// db.
    pub fn rebase(&mut self, new_blob: &[u8]) -> anyhow::Result<()> {
        let tempdir = IcingTempDir::new("pm-rebase");
        self.database = IcingMetaDatabase::import_with_changes(tempdir, new_blob, &self.database)?;
        Ok(())
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

    pub async fn add_memory(&mut self, mut memory: Memory) -> anyhow::Result<MemoryId> {
        self.add_memory_id(&mut memory);
        self.add_llm_view_ids(&mut memory);
        let blob_id = self.cache.add_memory(&memory).await?;
        self.meta_db().add_memory(&memory, blob_id)?;
        Ok(memory.id)
    }

    pub async fn get_memories_by_tag(
        &mut self,
        tag: &str,
        result_mask: &Option<ResultMask>,
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(Vec<Memory>, PageToken)> {
        let (all_blob_ids, next_page_token) =
            self.meta_db().get_memories_by_tag(tag, page_size, page_token)?;

        if all_blob_ids.is_empty() {
            return Ok((Vec::new(), PageToken::Start));
        }

        let mut memories = self.cache.get_memories_by_blob_ids(&all_blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, result_mask);

        Ok((memories, next_page_token))
    }

    pub async fn get_memory_by_id(
        &mut self,
        id: MemoryId,
        result_mask: &Option<ResultMask>,
    ) -> anyhow::Result<Option<Memory>> {
        if let Some(blob_id) = self.meta_db().get_blob_id_by_memory_id(id.clone())? {
            self.cache.get_memory_by_blob_id(&blob_id).await.map(|mut m| {
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
        let _ = self.meta_db().reset();
        Ok(())
    }

    pub async fn search_memory(
        &mut self,
        request: SearchMemoryRequest,
    ) -> anyhow::Result<(Vec<SearchMemoryResultItem>, PageToken)> {
        let query = request.query.as_ref().context("the query must be non-empty")?;
        let page_token = PageToken::try_from(request.page_token)
            .map_err(|e| anyhow::anyhow!("Invalid page token: {}", e))?;
        let (search_results, next_page_token) =
            self.meta_db().search(query, request.page_size, page_token)?;

        if search_results.items.is_empty() {
            return Ok((Vec::new(), next_page_token));
        }

        let blob_ids: Vec<BlobId> =
            search_results.items.iter().map(|item| item.blob_id.clone()).collect();
        let mut memories = self.cache.get_memories_by_blob_ids(&blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, &request.result_mask);

        let results = memories
            .into_iter()
            .zip(search_results.items.into_iter())
            .map(|(mut memory, item)| {
                let score = item.score;
                let view_scores = item.view_scores;
                if !request.keep_all_llm_views {
                    let view_ids = item.view_ids;
                    if let Some(views) = memory.views.as_mut() {
                        let mut ordered_views = Vec::new();
                        for view_id in view_ids {
                            if let Some(view) = views.llm_views.iter().find(|v| v.id == view_id) {
                                ordered_views.push(view.clone());
                            }
                        }
                        views.llm_views = ordered_views;
                    }
                }
                SearchMemoryResultItem { memory: Some(memory), score, view_scores }
            })
            .collect();

        Ok((results, next_page_token))
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

    pub async fn delete_memories(&mut self, ids: Vec<MemoryId>) -> anyhow::Result<()> {
        self.meta_db().delete_memories(&ids)?;
        self.cache.delete_memories(&ids).await?;
        Ok(())
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
            if !mask.include_fields.contains(&(MemoryField::Embeddings as i32)) {
                memory.embeddings.clear();
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
            } else if !mask.include_content_fields.is_empty() {
                if let Some(content_struct) = memory.content.as_mut() {
                    // Filter the 'contents' map based on 'include_content_fields'.
                    content_struct
                        .contents
                        .retain(|key, _| mask.include_content_fields.contains(key));
                }
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
        prelude::v1::{Embedding, Memory, MemoryContent, MemoryField, MemoryValue, ResultMask},
    };

    use super::*;

    #[allow(deprecated)]
    fn create_memory_for_mask_test() -> Memory {
        Memory {
            id: "test_id".to_string(),
            tags: vec!["tag1".to_string(), "tag2".to_string()],
            embeddings: vec![Embedding::default()],
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
        }
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_no_mask() {
        let mut memory = create_memory_for_mask_test();
        let original_memory = memory.clone();
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &None);
        assert_eq!(memory, original_memory);
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_id() {
        let mut memory = create_memory_for_mask_test();
        let mask =
            Some(ResultMask { include_fields: vec![MemoryField::Id as i32], ..Default::default() });
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &mask);
        assert_eq!(memory.id, "test_id");
        assert!(memory.tags.is_empty());
        assert!(memory.embeddings.is_empty());
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
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert_eq!(memory.tags, vec!["tag1".to_string(), "tag2".to_string()]);
        assert!(memory.embeddings.is_empty());
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
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert!(memory.tags.is_empty());
        assert!(memory.embeddings.is_empty());
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
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert!(memory.tags.is_empty());
        assert!(memory.embeddings.is_empty());
        assert!(memory.content.is_none());
        assert!(memory.created_timestamp.is_some());
        assert!(memory.event_timestamp.is_some());
        assert!(memory.expiration_timestamp.is_some());
        assert!(memory.views.is_none());
    }

    #[test]
    #[allow(deprecated)]
    fn test_apply_mask_to_memory_include_views() {
        let mut memory = create_memory_for_mask_test();
        let mask = Some(ResultMask {
            include_fields: vec![MemoryField::Views as i32],
            ..Default::default()
        });
        DatabaseWithCache::apply_mask_to_memory(&mut memory, &mask);
        assert!(memory.id.is_empty());
        assert!(memory.tags.is_empty());
        assert!(memory.embeddings.is_empty());
        assert!(memory.content.is_none());
        assert!(memory.created_timestamp.is_none());
        assert!(memory.event_timestamp.is_none());
        assert!(memory.expiration_timestamp.is_none());
        assert!(memory.views.is_some());
    }
}
