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
use external_db_client::ExternalDbClient;
use rand::Rng;
use sealed_memory_rust_proto::prelude::v1::*;

use crate::{
    icing::{IcingMetaDatabase, PageToken},
    memory_cache::MemoryCache,
    MemoryId,
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

    /// Returns true if the cached database contains content that doesnt exist
    /// in durable storage, and should be written back.
    pub fn changed(&self) -> bool {
        self.database.needs_writeback()
    }

    pub async fn add_memory(&mut self, mut memory: Memory) -> anyhow::Result<MemoryId> {
        if memory.id.is_empty() {
            memory.id = rand::rng().random::<u64>().to_string();
        }
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
        if let Some(blob_id) = self.meta_db().get_blob_id_by_memory_id(id)? {
            self.cache.get_memory_by_blob_id(&blob_id).await.map(|mut m| {
                Self::apply_mask_to_memory(&mut m, result_mask);
                Some(m)
            })
        } else {
            Ok(None)
        }
    }

    pub async fn reset_memory(&mut self) -> bool {
        self.meta_db().reset();
        true
    }

    pub async fn search_memory(
        &mut self,
        request: SearchMemoryRequest,
    ) -> anyhow::Result<(Vec<SearchMemoryResultItem>, PageToken)> {
        let page_token = PageToken::try_from(request.page_token)
            .map_err(|e| anyhow::anyhow!("Invalid page token: {}", e))?;
        let (blob_ids, scores, next_page_token) = self.meta_db().search(
            &request.query.context("the query must be non-empty")?,
            request.page_size,
            page_token,
        )?;
        let mut memories = self.cache.get_memories_by_blob_ids(&blob_ids).await?;
        Self::apply_mask_to_memories(&mut memories, &request.result_mask);

        let results = memories
            .into_iter()
            .zip(scores.into_iter())
            .map(|(memory, _score)| SearchMemoryResultItem { memory: Some(memory) })
            .collect();
        Ok((results, next_page_token))
    }

    pub async fn delete_memories(&mut self, ids: Vec<MemoryId>) -> anyhow::Result<()> {
        self.meta_db().delete_memories(&ids)?;
        self.cache.delete_memories(&ids).await?;
        Ok(())
    }

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
