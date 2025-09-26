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

use anyhow::{bail, ensure, Context};
use external_db_client::BlobId;
use icing::{DocumentProto, IcingGroundTruthFilesHelper};
use log::{debug, error, info};
use prost::Message;
use rand::Rng;
use sealed_memory_rust_proto::{
    oak::private_memory::{
        search_memory_query, text_query, EmbeddingQuery, LlmView, MatchType, QueryClauses,
        QueryOperator, SearchMemoryQuery, TextQuery,
    },
    prelude::v1::*,
};

use crate::{MemoryId, ViewId};

fn timestamp_to_i64(timestamp: &prost_types::Timestamp) -> i64 {
    timestamp.seconds * 1_000_000_000 + (timestamp.nanos as i64)
}

// A simple struct to manage the temporary location of the icing database.
//
// The directory will be deleted when the struct is dropped, if possible. If
// deletion fails, an info message will be logged.
pub struct IcingTempDir {
    path: String,
}

impl IcingTempDir {
    // Create a new icing temp directory in std::env::temp_dir()
    pub fn new(prefix: &str) -> Self {
        let mut tmp = std::env::temp_dir();
        let random: u64 = rand::rng().random::<u64>();
        tmp.push(format!("{prefix}{random}"));
        Self { path: tmp.as_path().to_string_lossy().into() }
    }

    pub fn as_str(&self) -> &str {
        self.path.as_str()
    }
}

impl Drop for IcingTempDir {
    fn drop(&mut self) {
        match std::fs::remove_dir_all(&self.path) {
            Ok(()) => debug!("Successfully removed the icing directory at {:?}.", self.path),
            Err(e) => info!("Failed to remove the icing directory {:?}, {}", self.path, e),
        }
    }
}

/// The essential database that stores all the meta information
/// except the raw document content of a user.
///
/// The current schema is
/// {
///   "memory_id": string, indexable
///   "tags": repeated string, indexable
///   "blob_id": string
/// }
/// Indexable fields are the ones that can be searched against.
pub struct IcingMetaDatabase {
    // Note: icing_search_engine must come before base_dir, so that it is
    // dropped before the temp dir is dropped and deleted.
    icing_search_engine: cxx::UniquePtr<icing::IcingSearchEngine>,
    base_dir: IcingTempDir,
    applied_operations: Vec<MutationOperation>,
}

// `IcingMetaBase` is safe to send because it is behind a unique_ptr,
// but it is unsafe to sync because that will allow concurrent write accesses
// to the underlying icing database.
unsafe impl Send for IcingMetaDatabase {}
impl !Sync for IcingMetaDatabase {}

const NAMESPACE_NAME: &str = "namespace";
const SCHMA_NAME: &str = "Memory";
const TAG_NAME: &str = "tag";
const MEMORY_ID_NAME: &str = "memoryId";
const BLOB_ID_NAME: &str = "blobId";
const EMBEDDING_NAME: &str = "embedding";
const CREATED_TIMESTAMP_NAME: &str = "createdTimestamp";
const EVENT_TIMESTAMP_NAME: &str = "eventTimestamp";

const LLM_VIEW_SCHEMA_NAME: &str = "LlmView";
const VIEW_ID_NAME: &str = "viewId";

/// A representation of a mutation operation.
/// These are used to track changes that have been applied to the local
/// in-memory metadata database, but not yet committed to durable storage.
#[allow(dead_code)]
enum MutationOperation {
    // No action for this one, it just indicates that the database was newly created.
    Create,

    // A new item was added. The content blob will have been written separately, this operation
    // contains only the metadata changes that need to be re-written to a new database version on
    // version conflicts.
    AddMemory(PendingMetadata),
    AddView(PendingLlmViewMetadata),

    // The item with the given ID was removed.
    // Note that exact operation timing is not maintained. So if another session
    // wrote this ID later than the remove occurred, but wrote its metadatabase
    // back earlier, this remove would still result in removing the item.
    Remove(MemoryId),

    // The entire metadata database was reset.
    // Note that exact operation timing is not maintained.
    Reset,
}

/// The generated metadata for a memory.
/// This contains the information needed to write the metadata to the icing
/// database.
#[derive(Debug, Clone)]
struct PendingMetadata {
    icing_document: DocumentProto,
}

impl PendingMetadata {
    #[allow(deprecated)]
    pub fn new(memory: &Memory, blob_id: &BlobId) -> Self {
        let memory_id = &memory.id;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let embeddings: Vec<_> = memory
            .embeddings
            .iter()
            .map(|x| icing::create_vector_proto(x.model_signature.as_str(), &x.values))
            .collect();
        let document_builder = icing::create_document_builder();
        let document_builder = document_builder
            .set_key(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes())
            .set_schema(SCHMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()])
            .add_vector_property(EMBEDDING_NAME.as_bytes(), &embeddings);

        if let Some(ref created_timestamp) = memory.created_timestamp {
            document_builder.add_int64_property(
                CREATED_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(created_timestamp),
            );
        }
        if let Some(ref event_timestamp) = memory.event_timestamp {
            document_builder.add_int64_property(
                EVENT_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(event_timestamp),
            );
        }
        let icing_document = document_builder.build();
        Self { icing_document }
    }

    pub fn document(&self) -> &DocumentProto {
        &self.icing_document
    }
}

/// The generated metadata for a memory.
/// This contains the information needed to write the metadata to the icing
/// database.
#[derive(Debug, Clone)]
struct PendingLlmViewMetadata {
    icing_document: DocumentProto,
}

impl PendingLlmViewMetadata {
    pub fn new(memory: &Memory, view: &LlmView, blob_id: &BlobId) -> Option<Self> {
        let memory_id = &memory.id;
        let view_id = &view.id;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let embedding = view.embedding.as_ref()?;
        let embeddings =
            vec![icing::create_vector_proto(embedding.model_signature.as_str(), &embedding.values)];
        let document_builder = icing::create_document_builder();
        let document_builder = document_builder
            .set_key(NAMESPACE_NAME.as_bytes(), view_id.as_bytes())
            .set_schema(LLM_VIEW_SCHEMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(VIEW_ID_NAME.as_bytes(), &[view_id.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()])
            .add_vector_property(EMBEDDING_NAME.as_bytes(), &embeddings);

        if let Some(ref created_timestamp) = memory.created_timestamp {
            document_builder.add_int64_property(
                CREATED_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(created_timestamp),
            );
        }
        if let Some(ref event_timestamp) = memory.event_timestamp {
            document_builder.add_int64_property(
                EVENT_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(event_timestamp),
            );
        }
        let icing_document = document_builder.build();
        Some(Self { icing_document })
    }

    pub fn document(&self) -> &DocumentProto {
        &self.icing_document
    }
}

#[derive(Debug, Default)]
pub struct SearchResultId {
    pub blob_id: BlobId,
    pub view_ids: Vec<ViewId>,
    pub score: f32,
}

#[derive(Debug, Default)]
pub struct SearchResultIds {
    pub items: Vec<SearchResultId>,
}

impl IcingMetaDatabase {
    /// Creates a ResultSpecProto projection to retrieve only the blob ids.
    fn create_blob_id_projection(schema_name: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![BLOB_ID_NAME.to_string()],
        }
    }

    fn extract_blob_ids_from_search_result(search_result: icing::SearchResultProto) -> Vec<BlobId> {
        search_result.results.iter().filter_map(Self::extract_blob_id_from_doc).collect::<Vec<_>>()
    }

    fn create_search_filter(schema_name: &str, path: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![path.to_string()],
        }
    }

    fn create_schema() -> icing::SchemaProto {
        let schema_type_builder = icing::create_schema_type_config_builder();
        schema_type_builder
            .set_type(SCHMA_NAME.as_bytes())
            .add_property(
                icing::create_property_config_builder()
                    .set_name(TAG_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Plain.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Repeated.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(MEMORY_ID_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Plain.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(BLOB_ID_NAME.as_bytes())
                    // We don't need to index blob id
                    // TODO: yongheng - Use String type instead of Int64.
                    .set_data_type(icing::property_config_proto::data_type::Code::Int64.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(EMBEDDING_NAME.as_bytes())
                    .set_data_type_vector(
                        icing::embedding_indexing_config::embedding_indexing_type::Code::LinearSearch.into(),
                    )
                    .set_cardinality(icing::property_config_proto::cardinality::Code::Repeated.into())
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(CREATED_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(icing::integer_indexing_config::numeric_match_type::Code::Range.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(EVENT_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(icing::integer_indexing_config::numeric_match_type::Code::Range.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            );

        let memory_view_schema_type_builder = icing::create_schema_type_config_builder();
        memory_view_schema_type_builder
            .set_type(LLM_VIEW_SCHEMA_NAME.as_bytes())
            .add_property(
                icing::create_property_config_builder()
                    .set_name(TAG_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Plain.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Repeated.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(MEMORY_ID_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Plain.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(VIEW_ID_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Plain.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(BLOB_ID_NAME.as_bytes())
                    // We don't need to index blob id
                    .set_data_type(icing::property_config_proto::data_type::Code::String.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(EMBEDDING_NAME.as_bytes())
                    .set_data_type_vector(
                        icing::embedding_indexing_config::embedding_indexing_type::Code::LinearSearch.into(),
                    )
                    .set_cardinality(icing::property_config_proto::cardinality::Code::Optional.into())
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(CREATED_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(icing::integer_indexing_config::numeric_match_type::Code::Range.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(EVENT_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(icing::integer_indexing_config::numeric_match_type::Code::Range.into())
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            );

        let schema_builder = icing::create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        schema_builder.add_type(&memory_view_schema_type_builder);
        schema_builder.build()
    }

    /// Create a new icing database in `base_dir`. If there is already a icing
    /// db in `base_dir`, the old one will be deleted.
    pub fn new(base_dir: IcingTempDir) -> anyhow::Result<Self> {
        debug!("Creating new icing database in {}", base_dir.as_str());
        let icing_search_engine = Self::initialize_icing_database(base_dir.as_str())?;
        let schema = Self::create_schema();
        let result_proto = icing_search_engine.set_schema(&schema);
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        Ok(Self {
            icing_search_engine,
            base_dir,
            applied_operations: vec![MutationOperation::Create],
        })
    }

    /// Create a new icing database in `base_dir`. Using the provided import
    /// data.
    pub fn import(base_dir: IcingTempDir, data: impl bytes::Buf) -> anyhow::Result<Self> {
        debug!("Importing icing database into {}", base_dir.as_str());
        let ground_truth = icing::IcingGroundTruthFiles::decode(data)?;
        ground_truth.migrate(base_dir.as_str())?;

        let icing_search_engine = Self::initialize_icing_database(base_dir.as_str())?;
        Ok(Self { icing_search_engine, base_dir, applied_operations: vec![] })
    }

    fn initialize_icing_database(
        base_dir_str: &str,
    ) -> anyhow::Result<cxx::UniquePtr<icing::IcingSearchEngine>> {
        let options_bytes = icing::get_default_icing_options(base_dir_str).encode_to_vec();
        let icing_search_engine = icing::create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize();
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        Ok(icing_search_engine)
    }

    // Adds a new memory to the cache.
    // The generated metadta is returned so that it can be re-applied if needed.
    pub fn add_memory(&mut self, memory: &Memory, blob_id: BlobId) -> anyhow::Result<()> {
        let pending_metadata = PendingMetadata::new(memory, &blob_id);
        self.add_pending_metadata(pending_metadata)?;
        if let Some(views) = memory.views.as_ref() {
            for view in &views.llm_views {
                // TODO: yongheng - Generate view id if not provided.
                if let Some(pending_view_metadata) =
                    PendingLlmViewMetadata::new(memory, view, &blob_id)
                {
                    self.add_pending_memory_view_metadata(pending_view_metadata)?;
                }
            }
        }
        Ok(())
    }

    fn add_pending_memory_view_metadata(
        &mut self,
        pending_metadata: PendingLlmViewMetadata,
    ) -> anyhow::Result<()> {
        let result = self.icing_search_engine.put(pending_metadata.document());
        if result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            debug!("{:?}", result);
        }
        ensure!(
            result.status.context("no status")?.code == Some(icing::status_proto::Code::Ok.into())
        );
        self.applied_operations.push(MutationOperation::AddView(pending_metadata));
        Ok(())
    }

    fn add_pending_metadata(&mut self, pending_metadata: PendingMetadata) -> anyhow::Result<()> {
        let result = self.icing_search_engine.put(pending_metadata.document());
        if result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            debug!("{:?}", result);
        }
        ensure!(
            result.status.context("no status")?.code == Some(icing::status_proto::Code::Ok.into())
        );
        self.applied_operations.push(MutationOperation::AddMemory(pending_metadata));
        Ok(())
    }

    pub fn get_memories_by_tag(
        &self,
        tag: &str,
        mut page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(Vec<BlobId>, PageToken)> {
        if page_token == PageToken::Invalid {
            bail!("Invalid page token provided");
        }

        let search_spec = icing::SearchSpecProto {
            query: Some(tag.to_string()),
            // Match exactly as defined in the schema for tags.
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            // Match only Memory Schema.
            schema_type_filters: vec![SCHMA_NAME.to_string()],
            type_property_filters: vec![Self::create_search_filter(SCHMA_NAME, TAG_NAME)],
            ..Default::default()
        };

        // Default to 10 if page size is 0.
        if page_size <= 0 {
            page_size = 10;
        }

        let result_spec = icing::ResultSpecProto {
            // Request a large number to get all results in one go for simplicity.
            // Consider pagination for very large datasets.
            num_per_page: Some(page_size),
            type_property_masks: vec![Self::create_blob_id_projection(SCHMA_NAME)],
            ..Default::default()
        };

        let search_result: icing::SearchResultProto = match page_token {
            PageToken::Start => self.icing_search_engine.search(
                &search_spec,
                &icing::get_default_scoring_spec(), // Use default scoring for now
                &result_spec,
            ),
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token),
            PageToken::Invalid => unreachable!(), // Already handled
        };

        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed: {:?}", search_result.status);
        }

        let next_page_token =
            search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
        let blob_ids = Self::extract_blob_ids_from_search_result(search_result);
        if blob_ids.is_empty() {
            return Ok((blob_ids, PageToken::Start));
        }
        Ok((blob_ids, next_page_token))
    }

    pub fn get_blob_id_by_memory_id(&self, memory_id: MemoryId) -> anyhow::Result<Option<BlobId>> {
        let search_spec = icing::SearchSpecProto {
            query: Some(memory_id.to_string()),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHMA_NAME.to_string()],
            type_property_filters: vec![Self::create_search_filter(SCHMA_NAME, MEMORY_ID_NAME)],
            ..Default::default()
        };

        let result_spec = icing::ResultSpecProto {
            num_per_page: Some(1), // We expect at most one result
            type_property_masks: vec![Self::create_blob_id_projection(SCHMA_NAME)],
            ..Default::default()
        };

        let search_result: icing::SearchResultProto = self.icing_search_engine.search(
            &search_spec,
            &icing::get_default_scoring_spec(), // Scoring doesn't matter much here
            &result_spec,
        );

        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for memory_id {}: {:?}", memory_id, search_result.status);
        }

        // Extract the blob_id (int64) from the first result, if any
        Ok(search_result.results.first().and_then(Self::extract_blob_id_from_doc))
    }

    fn extract_blob_id_from_doc(
        doc_hit: &icing::search_result_proto::ResultProto,
    ) -> Option<BlobId> {
        let blob_id_name = BLOB_ID_NAME.to_string();
        doc_hit
            .document
            .as_ref()?
            .properties
            .iter()
            .find(|prop| prop.name.as_ref() == Some(&blob_id_name))?
            .string_values
            .first()
            .cloned()
    }

    fn extract_view_id_from_doc(
        doc_hit: &icing::search_result_proto::ResultProto,
    ) -> Option<ViewId> {
        let view_id_name = VIEW_ID_NAME.to_string();
        doc_hit
            .document
            .as_ref()?
            .properties
            .iter()
            .find(|prop| prop.name.as_ref() == Some(&view_id_name))?
            .string_values
            .first()
            .cloned()
    }

    fn extract_memory_id_from_doc(
        doc_hit: &icing::search_result_proto::ResultProto,
    ) -> Option<MemoryId> {
        let memory_id_name = MEMORY_ID_NAME.to_string();
        doc_hit
            .document
            .as_ref()?
            .properties
            .iter()
            .find(|prop| prop.name.as_ref() == Some(&memory_id_name))?
            .string_values
            .first()
            .cloned()
    }

    fn extract_memory_ids_from_search_result(
        search_result: icing::SearchResultProto,
    ) -> Vec<MemoryId> {
        search_result
            .results
            .iter()
            .filter_map(Self::extract_memory_id_from_doc)
            .collect::<Vec<_>>()
    }

    fn create_memory_id_projection(schema_name: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![MEMORY_ID_NAME.to_string()],
        }
    }

    pub fn get_all_memory_ids(&self) -> anyhow::Result<Vec<MemoryId>> {
        // Search for all memories.
        let mut all_memory_ids = Vec::new();
        let mut page_token = PageToken::Start;
        loop {
            let search_spec = icing::SearchSpecProto {
                query: Some(format!("({} >= 0)", CREATED_TIMESTAMP_NAME)),
                enabled_features: vec!["NUMERIC_SEARCH".to_string()],
                term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
                schema_type_filters: vec![SCHMA_NAME.to_string()],
                ..Default::default()
            };
            let result_spec = icing::ResultSpecProto {
                num_per_page: Some(1000), // Max page size
                type_property_masks: vec![Self::create_memory_id_projection(SCHMA_NAME)],
                ..Default::default()
            };
            let search_result: icing::SearchResultProto = match page_token {
                PageToken::Start => self.icing_search_engine.search(
                    &search_spec,
                    &icing::get_default_scoring_spec(),
                    &result_spec,
                ),
                PageToken::Token(token) => self.icing_search_engine.get_next_page(token),
                PageToken::Invalid => bail!("Invalid page token"),
            };

            if search_result.status.clone().context("no status")?.code
                != Some(icing::status_proto::Code::Ok.into())
            {
                bail!("Icing search failed: {:?}", search_result.status);
            }

            let memory_ids = Self::extract_memory_ids_from_search_result(search_result.clone());
            all_memory_ids.extend(memory_ids);

            let next_page_token =
                search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
            if next_page_token == PageToken::Start {
                break;
            }
            page_token = next_page_token;
        }
        Ok(all_memory_ids)
    }

    pub fn reset(&mut self) {
        self.icing_search_engine.reset();
        let schema = Self::create_schema();
        self.icing_search_engine.set_schema(&schema);
        self.applied_operations.push(MutationOperation::Reset);
    }

    fn execute_search(
        &self,
        search_spec: &icing::SearchSpecProto,
        scoring_spec: &icing::ScoringSpecProto,
        page_size: i32,
        page_token: PageToken,
        result_projection: icing::TypePropertyMask,
    ) -> anyhow::Result<(icing::SearchResultProto, PageToken)> {
        const DEFAULT_LIMIT: i32 = 10;
        let limit = if page_size > 0 { page_size } else { DEFAULT_LIMIT };

        let mut result_spec =
            icing::ResultSpecProto { num_per_page: Some(limit), ..Default::default() };

        result_spec.type_property_masks.push(result_projection);

        let search_result = match page_token {
            PageToken::Start => {
                self.icing_search_engine.search(search_spec, scoring_spec, &result_spec)
            }
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token),
            PageToken::Invalid => bail!("invalid page token"),
        };

        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for {:?}", search_result.status);
        }

        let next_page_token =
            search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
        Ok((search_result, next_page_token))
    }

    pub fn search(
        &self,
        query: &SearchMemoryQuery,
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(SearchResultIds, PageToken)> {
        let search_views = Self::is_embedding_search(query);
        let (schema_name, projection) = if search_views {
            (
                LLM_VIEW_SCHEMA_NAME,
                icing::TypePropertyMask {
                    schema_type: Some(LLM_VIEW_SCHEMA_NAME.to_string()),
                    paths: vec![BLOB_ID_NAME.to_string(), VIEW_ID_NAME.to_string()],
                },
            )
        } else {
            (
                SCHMA_NAME,
                icing::TypePropertyMask {
                    schema_type: Some(SCHMA_NAME.to_string()),
                    paths: vec![BLOB_ID_NAME.to_string()],
                },
            )
        };

        let (search_spec, scoring_spec) = self.build_query_specs(query, schema_name)?;
        let scoring_spec = scoring_spec.unwrap_or_default();
        let mut page_token = page_token;
        let mut id_maps: HashMap<BlobId, Vec<ViewId>> = HashMap::new();
        let mut scores = HashMap::new();
        // When embedding search is used, we are matching against views instead
        // of memories. Therefore, we might match mulitple views of the same memory.
        // We need to aggregate the results and scores by memory id.
        // The tricky part is how we handle pagination. We want to return
        // `page_size` results to the user, but we need to keep searching to
        // find views for the same memory. We can't just search for `page_size`
        // because we don't know which memories the user has already seen.
        // Therefore, we keep search for one view until we find `page_size`
        // distinct memories.
        // Icing provides a new api called `get_next_page` that allows us to
        // some items of a page instead of the whole page. But the OSS version
        // does not have it yet.
        // TODO: yongheng - Add support for Icing's new get_next_page api.
        loop {
            let item_to_search = if search_views { 1 } else { page_size };
            let (search_result, next_page_token) = self.execute_search(
                &search_spec,
                &scoring_spec,
                item_to_search,
                page_token,
                projection.clone(),
            )?;
            page_token = next_page_token;

            if search_views {
                for result in &search_result.results {
                    if let (Some(blob_id), Some(view_id), score) = (
                        Self::extract_blob_id_from_doc(result),
                        Self::extract_view_id_from_doc(result),
                        result.score.map(|s| s as f32).unwrap_or(0.0),
                    ) {
                        id_maps.entry(blob_id.clone()).or_default().push(view_id);
                        *scores.entry(blob_id).or_default() += score;
                    }
                }
                if id_maps.keys().len() == page_size as usize || page_token == PageToken::Start {
                    break;
                }
            } else {
                let blob_ids = Self::extract_blob_ids_from_search_result(search_result);
                for blob_id in blob_ids.into_iter() {
                    id_maps.insert(blob_id, Vec::default());
                }
                break;
            }
        }

        let mut search_result_ids = SearchResultIds::default();

        for (blob_id, view_ids) in id_maps.into_iter() {
            let score = scores.get(&blob_id).unwrap_or(&0.0);
            search_result_ids.items.push(SearchResultId { blob_id, view_ids, score: *score });
        }
        search_result_ids
            .items
            .sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap_or(std::cmp::Ordering::Less));

        Ok((search_result_ids, page_token))
    }

    fn is_embedding_search(query: &SearchMemoryQuery) -> bool {
        match query.clause.as_ref() {
            Some(search_memory_query::Clause::EmbeddingQuery(_)) => true,
            Some(search_memory_query::Clause::QueryClauses(clauses)) => {
                clauses.clauses.iter().any(Self::is_embedding_search)
            }
            _ => false,
        }
    }

    fn build_query_specs(
        &self,
        query: &SearchMemoryQuery,
        schema_name: &str,
    ) -> anyhow::Result<(icing::SearchSpecProto, Option<icing::ScoringSpecProto>)> {
        match query.clause.as_ref().context("no clause")? {
            search_memory_query::Clause::TextQuery(text_query) => {
                self.build_text_query_specs(text_query, schema_name)
            }
            search_memory_query::Clause::EmbeddingQuery(embedding_query) => {
                self.build_embedding_query_specs(embedding_query, schema_name)
            }
            search_memory_query::Clause::QueryClauses(clauses) => {
                self.build_clauses_query_specs(clauses, schema_name)
            }
        }
    }

    fn build_clauses_query_specs(
        &self,
        clauses: &QueryClauses,
        schema_name: &str,
    ) -> anyhow::Result<(icing::SearchSpecProto, Option<icing::ScoringSpecProto>)> {
        let operator = match clauses.query_operator() {
            QueryOperator::And => "AND",
            QueryOperator::Or => "OR",
            _ => bail!("unsupported operator"),
        };

        let mut sub_queries = Vec::new();
        let mut score_spec = icing::ScoringSpecProto::default();
        let mut embedding_vectors = Vec::new();
        let mut metric_type = None;
        for clause in &clauses.clauses {
            let (spec, sub_score_spec) = self.build_query_specs(clause, schema_name)?;
            if let Some(sub_score_spec) = sub_score_spec {
                score_spec = sub_score_spec;
            }
            if spec.embedding_query_metric_type.is_some() {
                metric_type = spec.embedding_query_metric_type;
            }
            sub_queries.push(format!("({})", spec.query.context("no sub query")?));
            embedding_vectors.extend(spec.embedding_query_vectors);
        }

        let query = sub_queries.join(&format!(" {} ", operator));
        let mut search_spec = icing::SearchSpecProto {
            query: Some(query),
            embedding_query_vectors: embedding_vectors,
            embedding_query_metric_type: metric_type,
            enabled_features: vec![
                "NUMERIC_SEARCH".to_string(),
                icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
            ],
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            ..Default::default()
        };
        if !schema_name.is_empty() {
            search_spec.schema_type_filters.push(schema_name.to_string());
        }
        Ok((search_spec, Some(score_spec)))
    }

    fn build_text_query_specs(
        &self,
        text_query: &TextQuery,
        schema_name: &str,
    ) -> anyhow::Result<(icing::SearchSpecProto, Option<icing::ScoringSpecProto>)> {
        let value =
            if let Some(text_query::Value::TimestampVal(timestamp)) = text_query.value.as_ref() {
                timestamp_to_i64(timestamp).to_string()
            } else if let Some(text_query::Value::StringVal(text)) = text_query.value.as_ref() {
                text.to_string()
            } else {
                bail!("unsupported value type for text search");
            };

        let field_name = match text_query.field() {
            MemoryField::CreatedTimestamp => CREATED_TIMESTAMP_NAME,
            MemoryField::EventTimestamp => EVENT_TIMESTAMP_NAME,
            MemoryField::Id => MEMORY_ID_NAME,
            MemoryField::Tags => TAG_NAME,
            _ => bail!("unsupported field for text search"),
        };

        let query = match text_query.match_type() {
            MatchType::Equal => {
                if field_name == CREATED_TIMESTAMP_NAME || field_name == EVENT_TIMESTAMP_NAME {
                    format!("({field_name} == {value})")
                } else {
                    format!("({field_name}:{value})")
                }
            }
            MatchType::Gte => format!("({field_name} >= {value})"),
            MatchType::Lte => format!("({field_name} <= {value})"),
            MatchType::Gt => format!("({field_name} > {value})"),
            MatchType::Lt => format!("({field_name} < {value})"),
            _ => bail!("unsupported match type for text search"),
        };

        let mut search_spec = icing::SearchSpecProto {
            query: Some(query),
            enabled_features: vec!["NUMERIC_SEARCH".to_string()],
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            ..Default::default()
        };
        if !schema_name.is_empty() {
            search_spec.schema_type_filters.push(schema_name.to_string());
        }
        Ok((search_spec, None))
    }

    fn build_scoring_spec(&self) -> icing::ScoringSpecProto {
        // Caculate the sum of the scores of all matching embeddings.
        const SUM_ALL_MATCHING_EMBEDDING: &str =
            "sum(this.matchedSemanticScores(getEmbeddingParameter(0)))";
        let mut scoring_spec = icing::get_default_scoring_spec();
        scoring_spec.rank_by = Some(
            icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
        );
        scoring_spec.advanced_scoring_expression = Some(SUM_ALL_MATCHING_EMBEDDING.to_string());
        scoring_spec
    }

    fn build_embedding_query_specs(
        &self,
        embedding_query: &EmbeddingQuery,
        schema_name: &str,
    ) -> anyhow::Result<(icing::SearchSpecProto, Option<icing::ScoringSpecProto>)> {
        let query_embeddings: &[Embedding] = &embedding_query.embedding;
        let score_op: Option<ScoreRange> = embedding_query.score_range;

        // Search the first embedding property, specified by `EMBEDDING_NAME`.
        // Since we have only one embedding property, this is the one to go.
        let query_string = if let Some(score_op) = score_op {
            let score_min = score_op.min;
            let score_max = score_op.max;
            format!("semanticSearch(getEmbeddingParameter(0), {score_min}, {score_max})")
        } else {
            "semanticSearch(getEmbeddingParameter(0))".to_string()
        };

        let mut search_spec = icing::SearchSpecProto {
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            embedding_query_metric_type: Some(
                icing::search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
            ),

            embedding_query_vectors: query_embeddings
                .iter()
                .map(|x| icing::create_vector_proto(x.model_signature.as_str(), &x.values))
                .collect(),

            query: Some(query_string),
            enabled_features: vec![icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()],
            ..Default::default()
        };
        if !schema_name.is_empty() {
            search_spec.schema_type_filters.push(schema_name.to_string());
        }

        Ok((search_spec, Some(self.build_scoring_spec())))
    }

    /// Search based on the document embedding.
    /// The process is as follow:
    /// 1. For each memory, we find all the document embeddings that matches the
    ///    name of the search embedding, say `[doc_embeding1, doc_embedding2,
    ///    ...]`.
    /// 2. Perform a dot product on `search_embedding` and the matched
    ///    `[doc1_embedding, ...]`, which gives a list of scores `[score1,
    ///    score2, ...]`.
    /// 3. Sum the scores, and the corresponding memory has the final score
    ///    `score_sum`.
    /// 4. We repeat 1-3 for all memories, rank the memories by `score_sum`, and
    ///    return the first `limit` ones with highest scores.
    pub fn embedding_search(
        &self,
        embedding_query: &EmbeddingQuery,
        page_size: i32,
        page_token: PageToken,
        search_views: bool,
    ) -> anyhow::Result<(Vec<BlobId>, Vec<f32>, PageToken)> {
        let (schema_name, id_name) = if search_views {
            (LLM_VIEW_SCHEMA_NAME, BLOB_ID_NAME)
        } else {
            (SCHMA_NAME, BLOB_ID_NAME)
        };
        let (search_spec, scoring_spec) =
            self.build_embedding_query_specs(embedding_query, schema_name)?;

        let projection = icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![id_name.to_string()],
        };

        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &scoring_spec.unwrap_or_default(),
            page_size,
            page_token,
            projection,
        )?;

        let scores: Vec<f32> = search_result
            .results
            .iter()
            .map(|x| x.score.map(|s| s as f32).unwrap_or(0.0))
            .collect();

        let ids = Self::extract_blob_ids_from_search_result(search_result);
        ensure!(ids.len() == scores.len());
        if ids.is_empty() {
            return Ok((ids, scores, PageToken::Start));
        }
        Ok((ids, scores, next_page_token))
    }

    pub fn text_search(
        &self,
        text_query: &TextQuery,
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(SearchResultIds, PageToken)> {
        let (search_spec, _) = self.build_text_query_specs(text_query, SCHMA_NAME)?;
        let projection = Self::create_blob_id_projection(SCHMA_NAME);
        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &icing::ScoringSpecProto::default(),
            page_size,
            page_token,
            projection,
        )?;
        let scores: Vec<f32> = search_result
            .results
            .iter()
            .map(|x| x.score.map(|s| s as f32).unwrap_or(0.0))
            .collect();
        let ids = Self::extract_blob_ids_from_search_result(search_result);
        ensure!(ids.len() == scores.len());
        if ids.is_empty() {
            return Ok((SearchResultIds::default(), PageToken::Start));
        }
        let search_result_ids = SearchResultIds {
            items: ids
                .into_iter()
                .map(|id| SearchResultId { blob_id: id, ..Default::default() })
                .collect(),
        };
        Ok((search_result_ids, next_page_token))
    }

    pub fn delete_memories(&mut self, memory_ids: &[MemoryId]) -> anyhow::Result<()> {
        for memory_id in memory_ids {
            // TODO: b/447637766 - Delete the views associated with the memory.
            let result =
                self.icing_search_engine.delete(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes());
            if result.status.clone().context("no status")?.code
                != Some(icing::status_proto::Code::Ok.into())
            {
                bail!("Failed to delete memory with id {}: {:?}", memory_id, result.status);
            }
            self.applied_operations.push(MutationOperation::Remove(memory_id.clone()));
        }
        Ok(())
    }

    /// Returns true if this instance was created fresh, without any previously
    /// existing data.
    pub fn needs_writeback(&self) -> bool {
        !self.applied_operations.is_empty()
    }

    // Return a new [`IcingMetadataBase`] instance that contains all changes applied
    // to this one, but on top of a new base blob.
    //
    // The current instance is consumed, and a new one is returned.
    //
    // The expectation is that all operations can be applied without error.
    //
    // new_base_dir should be different that the base_dir for this instance,
    // otherwise unexpected errors may occur.
    //
    // If there is a failure when applying the new operation, no error will be
    // returning, but the error message will be logged.
    pub fn import_with_changes(
        new_base_dir: IcingTempDir,
        new_base_blob: &[u8],
        apply_changes_from: &IcingMetaDatabase,
    ) -> anyhow::Result<Self> {
        let mut new_db = Self::import(new_base_dir, new_base_blob)?;

        // Apply each operation to the new database.
        // This will also recreate the applied operations on the new database as a side
        // effect, in case it also needs to be rebased.
        for operation in apply_changes_from.applied_operations.iter() {
            let result = match operation {
                MutationOperation::Create => {
                    // No action, now the database is created.
                    Ok(())
                }
                MutationOperation::AddMemory(pending_metadata) => {
                    new_db.add_pending_metadata(pending_metadata.clone())
                }
                MutationOperation::AddView(pending_view_metadata) => {
                    new_db.add_pending_memory_view_metadata(pending_view_metadata.clone())
                }
                MutationOperation::Remove(id) => new_db.delete_memories(&[id.to_string()]),
                MutationOperation::Reset => {
                    new_db.reset();
                    Ok(())
                }
            };

            if result.is_err() {
                error!("Warning: failed to apply operation onto new database")
            }
        }

        Ok(new_db)
    }

    pub fn export(&self) -> anyhow::Result<icing::IcingGroundTruthFiles> {
        let result_proto =
            self.icing_search_engine.persist_to_disk(icing::persist_type::Code::Full.into());
        let result_proto = icing::PersistToDiskResultProto::decode(result_proto.as_slice())?;
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        icing::IcingGroundTruthFiles::new(self.base_dir.as_str())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PageToken {
    Start,
    Token(u64),
    Invalid,
}

impl TryFrom<String> for PageToken {
    type Error = anyhow::Error;
    fn try_from(s: String) -> anyhow::Result<Self> {
        if s.is_empty() {
            Ok(PageToken::Start)
        } else {
            match s.parse::<u64>() {
                Ok(token) => Ok(PageToken::Token(token)),
                Err(_) => Ok(PageToken::Invalid),
            }
        }
    }
}

impl From<PageToken> for String {
    fn from(token: PageToken) -> Self {
        match token {
            PageToken::Start => "".to_string(),
            PageToken::Token(t) => t.to_string(),
            PageToken::Invalid => "".to_string(),
        }
    }
}

impl From<u64> for PageToken {
    fn from(token: u64) -> Self {
        PageToken::Token(token)
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use sealed_memory_rust_proto::oak::private_memory::LlmViews;

    use super::*;

    fn tempdir() -> IcingTempDir {
        IcingTempDir::new("icing-test-")
    }

    #[gtest]
    fn basic_icing_search_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let memory = Memory {
            id: "Thisisanid".to_string(),
            tags: vec!["the_tag".to_string()],
            ..Default::default()
        };
        let blob_id = 12345.to_string();
        icing_database.add_memory(&memory, blob_id.clone())?;
        let memory2 = Memory {
            id: "Thisisanid2".to_string(),
            tags: vec!["the_tag".to_string()],
            ..Default::default()
        };
        let blob_id2 = 12346.to_string();
        icing_database.add_memory(&memory2, blob_id2.clone())?;

        let (result, _) = icing_database.get_memories_by_tag("the_tag", 10, PageToken::Start)?;
        assert_that!(result, unordered_elements_are![eq(&blob_id), eq(&blob_id2)]);
        Ok(())
    }

    #[gtest]
    fn icing_import_export_test() -> anyhow::Result<()> {
        // Save the path to check for deletion later.
        let base_dir = tempdir();
        let base_dir_string = base_dir.as_str().to_string();
        let mut icing_database = IcingMetaDatabase::new(base_dir)?;

        let memory_id1 = "memory_id_export_1".to_string();
        let blob_id1 = 654321.to_string();
        let memory1 = Memory {
            id: memory_id1.clone(),
            tags: vec!["export_tag".to_string()],
            ..Default::default()
        };
        icing_database.add_memory(&memory1, blob_id1.clone())?;

        // Export the database
        let exported_data = icing_database.export()?.encode_to_vec();
        drop(icing_database); // Drop the original instance
        expect_false!(std::path::Path::new(base_dir_string.as_str()).exists());

        // Import into a new directory (or the same one after cleaning)
        let imported_database = IcingMetaDatabase::import(tempdir(), exported_data.as_slice())
            .expect("failed to import");

        // Verify data exists in the imported database
        expect_that!(
            imported_database.get_blob_id_by_memory_id(memory_id1)?,
            eq(&Some(blob_id1.clone()))
        );
        let (result, _) =
            imported_database.get_memories_by_tag("export_tag", 10, PageToken::Start)?;
        assert_that!(result, unordered_elements_are![eq(&blob_id1)]);
        Ok(())
    }

    #[gtest]
    fn icing_get_blob_id_by_memory_id_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let memory_id1 = "memory_id_1".to_string();
        let blob_id1 = 54321.to_string();
        let memory1 =
            Memory { id: memory_id1.clone(), tags: vec!["tag1".to_string()], ..Default::default() };
        icing_database.add_memory(&memory1, blob_id1.clone())?;

        let memory_id2 = "memory_id_2".to_string();
        let blob_id2 = 54322.to_string();
        let memory2 =
            Memory { id: memory_id2.clone(), tags: vec!["tag2".to_string()], ..Default::default() };
        icing_database.add_memory(&memory2, blob_id2.clone())?;

        // Test finding an existing blob ID
        expect_that!(icing_database.get_blob_id_by_memory_id(memory_id1)?, eq(&Some(blob_id1)));
        // Test finding another existing blob ID
        expect_that!(icing_database.get_blob_id_by_memory_id(memory_id2)?, eq(&Some(blob_id2)));
        // Test finding a non-existent blob ID
        expect_that!(
            icing_database.get_blob_id_by_memory_id("non_existent_id".to_string())?,
            eq(&None)
        );
        Ok(())
    }

    #[gtest]
    fn icing_embedding_search_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let memory_id1 = "memory_embed_1".to_string();
        let blob_id1 = 98765.to_string();
        let embedding1 = Embedding {
            model_signature: "test_model".to_string(),
            values: vec![1.0, 0.0, 0.0], // Vector pointing along x-axis
        };
        let memory1 = Memory {
            id: memory_id1.clone(),
            tags: vec!["embed_tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "view1".to_string(),
                    embedding: Some(embedding1),
                    ..Default::default()
                }],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory1, blob_id1.clone())?;

        let memory_id2 = "memory_embed_2".to_string();
        let blob_id2 = 98766.to_string();
        let embedding2 = Embedding {
            model_signature: "test_model".to_string(),
            values: vec![0.0, 1.0, 0.0], // Vector pointing along y-axis
        };
        let memory2 = Memory {
            id: memory_id2.clone(),
            tags: vec!["embed_tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "view2".to_string(),
                    embedding: Some(embedding2),
                    ..Default::default()
                }],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory2, blob_id2.clone())?;

        let embedding_query = SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
                embedding: vec![Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![0.9, 0.1, 0.0],
                }],
                ..Default::default()
            })),
        };
        // Query embedding close to embedding1
        let (results, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
        // Expect memory1 to be the top result due to higher dot product
        assert_that!(blob_ids, elements_are![eq(&blob_id1), eq(&blob_id2)]);
        // We could also assert on the score if needed, but ordering is often sufficient
        assert_that!(scores, elements_are![eq(&0.9), eq(&0.1)]);

        let (results, _) = icing_database.search(&embedding_query, 1, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
        // Expect memory1 to be the top result due to higher dot product
        assert_that!(blob_ids, elements_are![eq(&blob_id1)]);
        // We could also assert on the score if needed, but ordering is often sufficient
        assert_that!(scores, elements_are![eq(&0.9)]);
        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_add_memory() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(tempdir())?;
        let (_mid_a, bid_a) = add_test_memory(&mut db1, "A");
        let (_mid_b, bid_b) = add_test_memory(&mut db1, "B");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer adds E and F
        let mut db2 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        let (_mid_c, bid_c) = add_test_memory(&mut db2, "C");
        let (_mid_d, bid_d) = add_test_memory(&mut db2, "D");

        // First concurrent changer import and first changer adds G and H
        let mut db3 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        let (_mid_e, bid_e) = add_test_memory(&mut db3, "E");
        let (_mid_f, bid_f) = add_test_memory(&mut db3, "F");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let db3_prime =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        // Should contain all items.
        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((
                unordered_elements_are![
                    eq(bid_a.as_str()),
                    eq(bid_b.as_str()),
                    eq(bid_c.as_str()),
                    eq(bid_d.as_str()),
                    eq(bid_e.as_str()),
                    eq(bid_f.as_str()),
                ],
                eq(&PageToken::Start),
            ))
        );

        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_add_and_delete_memory() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(tempdir())?;
        let (_mid_a, bid_a) = add_test_memory(&mut db1, "A");
        let (mid_b, _mid_b) = add_test_memory(&mut db1, "B");
        let (mid_c, _bid_c) = add_test_memory(&mut db1, "C");
        let (_mid_d, bid_d) = add_test_memory(&mut db1, "D");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer removes B, adds E
        let mut db2 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        db2.delete_memories(&[mid_b.clone()])?;
        let (_mid_e, bid_e) = add_test_memory(&mut db2, "E");

        // Second concurrent changer import and first changer removes B and C, add F
        // The remove will be redundant, but should not cause error or failures.
        let mut db3 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        db3.delete_memories(&[mid_b.clone(), mid_c.clone()])?;
        let (_mid_f, bid_f) = add_test_memory(&mut db3, "F");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let db3_prime =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((
                unordered_elements_are![
                    eq(bid_a.as_str()),
                    // B and C were deleted.
                    eq(bid_d.as_str()),
                    eq(bid_e.as_str()),
                    eq(bid_f.as_str())
                ],
                eq(&PageToken::Start),
            ))
        );

        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_reset() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(tempdir())?;
        let (_mid_a, _bid_a) = add_test_memory(&mut db1, "A");
        let (mid_b, _bid_b) = add_test_memory(&mut db1, "B");
        let (_mid_c, _bid_c) = add_test_memory(&mut db1, "C");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer removes B, adds E
        let mut db2 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        db2.delete_memories(&[mid_b.clone()])?;
        let (_mid_e, _bid_e) = add_test_memory(&mut db2, "E");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // Second concurrent changer import and reset.
        let mut db3 = IcingMetaDatabase::import(tempdir(), db1_exported.as_slice())?;
        db3.reset();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let db3_prime =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((is_empty(), eq(&PageToken::Start),))
        );
        Ok(())
    }

    fn add_test_memory(db: &mut IcingMetaDatabase, suffix: &str) -> (MemoryId, BlobId) {
        let memory_id = format!("memory_id_{suffix}");
        let blob_id = format!("blob_id_{suffix}");
        db.add_memory(
            &Memory { id: memory_id.clone(), tags: vec!["tag".to_string()], ..Default::default() },
            blob_id.clone(),
        )
        .expect("failed to add memory");
        (memory_id, blob_id)
    }

    #[gtest]
    fn icing_deduplicate_search_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let model_signature = "test_model".to_string();
        let mut memories = vec![];
        for i in 0..5 {
            let memory_id = format!("memory_embed_{}", i);
            let blob_id = (1000 + i).to_string();
            let mut views = vec![];
            for j in 0..2 {
                let view_id = format!("view_{}_{}", i, j);
                let score = 1.0 - (i as f32 * 0.2 + j as f32 * 0.1);
                let embedding = Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![score, 0.0, 0.0],
                };
                views.push(LlmView {
                    id: view_id,
                    embedding: Some(embedding),
                    ..Default::default()
                });
            }
            let memory = Memory {
                id: memory_id,
                tags: vec!["embed_tag".to_string()],
                views: Some(LlmViews { llm_views: views }),
                ..Default::default()
            };
            icing_database.add_memory(&memory, blob_id.clone())?;
            memories.push((memory, blob_id));
        }

        let embedding_query = SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
                embedding: vec![Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![1.0, 0.0, 0.0],
                }],
                ..Default::default()
            })),
        };

        let (results, _) = icing_database.search(&embedding_query, 2, PageToken::Start)?;
        assert_that!(results.items, len(eq(2)));

        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();

        // The first two views have scores 1.0 and 0.9, so the score is 1.9. The
        // second two views have scores 0.8 and 0.7. But the first two views belong to
        // the first memory, so the final score is 1.9. The last two views
        // belong to the second memory, we only match one more view.
        // So we match three views to get two memories.
        assert_that!(blob_ids, elements_are![eq(&memories[0].1), eq(&memories[1].1)]);
        assert_that!(scores, elements_are![eq(&1.9), eq(&0.8)]);

        Ok(())
    }
}
