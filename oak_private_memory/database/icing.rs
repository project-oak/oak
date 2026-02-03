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
use std::{collections::HashMap, time::SystemTime};

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

/// Trait for building text queries based on MatchType.
trait TextQueryBuilder {
    fn build_timestamp_query(&self, field_name: &str, value: i64) -> anyhow::Result<String>;
    fn build_string_query(&self, field_name: &str, value: &str) -> anyhow::Result<String>;
}

/// Implementation of TextQueryBuilder for MatchType.
impl TextQueryBuilder for MatchType {
    fn build_timestamp_query(&self, field_name: &str, value: i64) -> anyhow::Result<String> {
        match self {
            MatchType::Equal => Ok(format!("({field_name} == {value})")),
            MatchType::Gte => Ok(format!("({field_name} >= {value})")),
            MatchType::Lte => Ok(format!("({field_name} <= {value})")),
            MatchType::Gt => Ok(format!("({field_name} > {value})")),
            MatchType::Lt => Ok(format!("({field_name} < {value})")),
            _ => bail!("unsupported match type {:?} for timestamp search", self),
        }
    }

    fn build_string_query(&self, field_name: &str, value: &str) -> anyhow::Result<String> {
        match self {
            MatchType::Equal => {
                if field_name == CREATED_TIMESTAMP_NAME
                    || field_name == EVENT_TIMESTAMP_NAME
                    || field_name == EXPIRATION_TIMESTAMP_NAME
                {
                    Ok(format!("({field_name} == {value})"))
                } else {
                    Ok(format!("({field_name}:{value})"))
                }
            }
            MatchType::Gte => Ok(format!("({field_name} >= {value})")),
            MatchType::Lte => Ok(format!("({field_name} <= {value})")),
            MatchType::Gt => Ok(format!("({field_name} > {value})")),
            MatchType::Lt => Ok(format!("({field_name} < {value})")),
            _ => bail!("unsupported match type {:?} for text search", self),
        }
    }
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
const SCHEMA_NAME: &str = "Memory";
const TAG_NAME: &str = "tag";
const MEMORY_ID_NAME: &str = "memoryId";
const BLOB_ID_NAME: &str = "blobId";
const EMBEDDING_NAME: &str = "embedding";
const CREATED_TIMESTAMP_NAME: &str = "createdTimestamp";
const EVENT_TIMESTAMP_NAME: &str = "eventTimestamp";
const EXPIRATION_TIMESTAMP_NAME: &str = "expirationTimestamp";

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
pub struct PendingMetadata {
    icing_document: DocumentProto,
}

impl PendingMetadata {
    #[allow(deprecated)]
    pub fn new(memory: &Memory, blob_id: &BlobId) -> anyhow::Result<Self> {
        let memory_id = &memory.id;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let document_builder = icing::create_document_builder();
        let document_builder = document_builder
            .set_key(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes())
            .set_schema(SCHEMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()]);

        if let Some(ref created_timestamp) = memory.created_timestamp {
            let timestamp_ms = (created_timestamp.seconds * 1000
                + i64::from(created_timestamp.nanos) / 1_000_000)
                as u64;
            // Set the document's creation timestamp for Icing's CreationTimestamp ranking
            document_builder.set_creation_timestamp_ms(timestamp_ms);
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
        if let Some(ref expiration_timestamp) = memory.expiration_timestamp {
            document_builder.add_int64_property(
                EXPIRATION_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(expiration_timestamp),
            );
        }
        let icing_document = document_builder.build()?;
        Ok(Self { icing_document })
    }

    pub fn document(&self) -> &DocumentProto {
        &self.icing_document
    }
}

/// The generated metadata for a memory.
/// This contains the information needed to write the metadata to the icing
/// database.
#[derive(Debug, Clone)]
pub struct PendingLlmViewMetadata {
    icing_document: DocumentProto,
}

impl PendingLlmViewMetadata {
    pub fn new(memory: &Memory, view: &LlmView, blob_id: &BlobId) -> anyhow::Result<Option<Self>> {
        let memory_id = &memory.id;
        let view_id = &view.id;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let embedding = if let Some(e) = view.embedding.as_ref() {
            e
        } else {
            return Ok(None);
        };
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
        if let Some(ref expiration_timestamp) = memory.expiration_timestamp {
            document_builder.add_int64_property(
                EXPIRATION_TIMESTAMP_NAME.as_bytes(),
                timestamp_to_i64(expiration_timestamp),
            );
        }
        let icing_document = document_builder.build()?;
        Ok(Some(Self { icing_document }))
    }

    pub fn document(&self) -> &DocumentProto {
        &self.icing_document
    }
}

pub fn calculate_memory_icing_size(memory: &Memory) -> anyhow::Result<usize> {
    let dummy_blob_id: BlobId = "0000000000000000".to_string();
    let pending_metadata = crate::icing::PendingMetadata::new(memory, &dummy_blob_id)?;
    let mut total_size = pending_metadata.document().encoded_len();

    if let Some(views) = memory.views.as_ref() {
        for view in &views.llm_views {
            if let Some(pending_view_metadata) =
                crate::icing::PendingLlmViewMetadata::new(memory, view, &dummy_blob_id)?
            {
                total_size += pending_view_metadata.document().encoded_len();
            }
        }
    }
    Ok(total_size)
}

#[derive(Debug, Default, PartialEq)]
pub struct SearchResultId {
    pub blob_id: BlobId,
    pub view_ids: Vec<ViewId>,
    pub score: f32,
    pub view_scores: Vec<f32>,
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

    fn create_schema() -> anyhow::Result<icing::SchemaProto> {
        let schema_type_builder = icing::create_schema_type_config_builder();
        schema_type_builder
            .set_type(SCHEMA_NAME.as_bytes())
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
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(CREATED_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(
                        icing::integer_indexing_config::numeric_match_type::Code::Range.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(EVENT_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(
                        icing::integer_indexing_config::numeric_match_type::Code::Range.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(EXPIRATION_TIMESTAMP_NAME.as_bytes())
                    .set_data_type_int64(
                        icing::integer_indexing_config::numeric_match_type::Code::Range.into(),
                    )
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
            ).add_property(
                icing::create_property_config_builder()
                    .set_name(EXPIRATION_TIMESTAMP_NAME.as_bytes())
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
        let schema = Self::create_schema()?;
        let result_proto = icing_search_engine.set_schema(&schema)?;
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
        let result_proto = icing_search_engine.initialize()?;
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        Ok(icing_search_engine)
    }

    // Adds a new memory to the cache.
    // The generated metadta is returned so that it can be re-applied if needed.
    pub fn add_memory(&mut self, memory: &Memory, blob_id: BlobId) -> anyhow::Result<()> {
        // Check if the memory already exists.
        if self.get_blob_id_by_memory_id(memory.id.clone())?.is_some() {
            // The memory already exists with a different blob id, so we need to delete it
            // to clear the views before adding it again.
            self.delete_memories([memory.id.clone()].as_ref())?;
        }
        let pending_metadata = PendingMetadata::new(memory, &blob_id)?;
        self.add_pending_metadata(pending_metadata)?;
        if let Some(views) = memory.views.as_ref() {
            for view in &views.llm_views {
                // TODO: yongheng - Generate view id if not provided.
                if let Some(pending_view_metadata) =
                    PendingLlmViewMetadata::new(memory, view, &blob_id)?
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
        let result = self.icing_search_engine.put(pending_metadata.document())?;
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
        let result = self.icing_search_engine.put(pending_metadata.document())?;
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

        let query_str = build_non_expired_query_str(TAG_NAME, tag);

        let search_spec = icing::SearchSpecProto {
            query: Some(query_str),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            enabled_features: vec![
                "NUMERIC_SEARCH".to_string(),
                icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
                icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string(),
            ],
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
            type_property_masks: vec![Self::create_blob_id_projection(SCHEMA_NAME)],
            ..Default::default()
        };

        let search_result: icing::SearchResultProto = match page_token {
            PageToken::Start => self.icing_search_engine.search(
                &search_spec,
                &icing::get_default_scoring_spec(), // Use default scoring for now
                &result_spec,
            )?,
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token)?,
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
        let query_str = build_non_expired_query_str(MEMORY_ID_NAME, &memory_id);

        let search_spec = icing::SearchSpecProto {
            query: Some(query_str),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            enabled_features: vec![
                "NUMERIC_SEARCH".to_string(),
                icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
                icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string(),
            ],
            ..Default::default()
        };

        let result_spec = icing::ResultSpecProto {
            num_per_page: Some(1), // We expect at most one result
            type_property_masks: vec![Self::create_blob_id_projection(SCHEMA_NAME)],
            ..Default::default()
        };

        let search_result: icing::SearchResultProto = self.icing_search_engine.search(
            &search_spec,
            &icing::get_default_scoring_spec(), // Scoring doesn't matter much here
            &result_spec,
        )?;

        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for memory_id {}: {:?}", memory_id, search_result.status);
        }

        // Extract the blob_id (int64) from the first result, if any
        Ok(search_result.results.first().and_then(Self::extract_blob_id_from_doc))
    }

    fn extract_view_ids_from_search_result(search_result: icing::SearchResultProto) -> Vec<ViewId> {
        search_result.results.iter().filter_map(Self::extract_view_id_from_doc).collect::<Vec<_>>()
    }

    pub fn optimize(&self) -> anyhow::Result<icing::OptimizeResultProto> {
        self.icing_search_engine.optimize()
    }

    fn create_view_id_projection(schema_name: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![VIEW_ID_NAME.to_string()],
        }
    }

    fn get_view_ids_by_memory_id(&self, memory_id: MemoryId) -> anyhow::Result<Vec<ViewId>> {
        let search_spec = icing::SearchSpecProto {
            query: Some(memory_id.clone()),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![LLM_VIEW_SCHEMA_NAME.to_string()],
            type_property_filters: vec![Self::create_search_filter(
                LLM_VIEW_SCHEMA_NAME,
                MEMORY_ID_NAME,
            )],
            ..Default::default()
        };
        let result_spec = icing::ResultSpecProto {
            num_per_page: Some(1000), // Max page size
            type_property_masks: vec![Self::create_view_id_projection(LLM_VIEW_SCHEMA_NAME)],
            ..Default::default()
        };
        let search_result: icing::SearchResultProto = self.icing_search_engine.search(
            &search_spec,
            &icing::get_default_scoring_spec(),
            &result_spec,
        )?;
        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for memory_id {}: {:?}", memory_id, search_result.status);
        }
        Ok(Self::extract_view_ids_from_search_result(search_result))
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
                schema_type_filters: vec![SCHEMA_NAME.to_string()],
                ..Default::default()
            };
            let result_spec = icing::ResultSpecProto {
                num_per_page: Some(1000), // Max page size
                type_property_masks: vec![Self::create_memory_id_projection(SCHEMA_NAME)],
                ..Default::default()
            };
            let search_result: icing::SearchResultProto = match page_token {
                PageToken::Start => self.icing_search_engine.search(
                    &search_spec,
                    &icing::get_default_scoring_spec(),
                    &result_spec,
                )?,
                PageToken::Token(token) => self.icing_search_engine.get_next_page(token)?,
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

    pub fn get_expired_memories_ids(
        &self,
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(Vec<MemoryId>, PageToken)> {
        let text_query = TextQuery {
            match_type: MatchType::Lt as i32,
            field: MemoryField::ExpirationTimestamp as i32,
            value: Some(text_query::Value::TimestampVal(system_time_to_timestamp(
                SystemTime::now(),
            ))),
        };
        let (search_spec, _) = self.build_text_query_specs(&text_query, SCHEMA_NAME)?;
        let projection = Self::create_memory_id_projection(SCHEMA_NAME);
        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &icing::ScoringSpecProto::default(),
            page_size,
            page_token,
            projection,
        )?;
        let ids = Self::extract_memory_ids_from_search_result(search_result.clone());
        if ids.is_empty() {
            Ok((ids, PageToken::Start))
        } else {
            Ok((ids, next_page_token))
        }
    }

    pub fn reset(&mut self) -> anyhow::Result<()> {
        self.icing_search_engine.reset();
        let schema = Self::create_schema()?;
        self.icing_search_engine.set_schema(&schema)?;
        self.applied_operations.push(MutationOperation::Reset);
        Ok(())
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
                self.icing_search_engine.search(search_spec, scoring_spec, &result_spec)?
            }
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token)?,
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
                SCHEMA_NAME,
                icing::TypePropertyMask {
                    schema_type: Some(SCHEMA_NAME.to_string()),
                    paths: vec![BLOB_ID_NAME.to_string()],
                },
            )
        };
        let (search_spec, scoring_spec) =
            self.build_query_specs_filtering_expired_memories(query, schema_name)?;
        let scoring_spec = scoring_spec.unwrap_or_default();
        let mut page_token = page_token;
        let mut id_maps: HashMap<BlobId, Vec<(ViewId, f32)>> = HashMap::new();
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
                        id_maps.entry(blob_id).or_default().push((view_id, score));
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

        for (blob_id, views) in id_maps.into_iter() {
            let mut view_ids = Vec::new();
            let mut view_scores = Vec::new();
            let mut total_score = 0.0;
            for (view_id, score) in views {
                view_ids.push(view_id);
                view_scores.push(score);
                total_score += score;
            }
            search_result_ids.items.push(SearchResultId {
                blob_id,
                view_ids,
                score: total_score,
                view_scores,
            });
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

    fn build_query_specs_filtering_expired_memories(
        &self,
        query: &SearchMemoryQuery,
        schema_name: &str,
    ) -> anyhow::Result<(icing::SearchSpecProto, Option<icing::ScoringSpecProto>)> {
        let (mut query_specs, score_spec) = self.build_query_specs(query, schema_name)?;

        // A memory is considered not expired if its expiration timestamp is in the
        // future, or if it has no expiration timestamp set.
        let now_ts = timestamp_to_i64(&system_time_to_timestamp(SystemTime::now()));
        query_specs.query = Some(format!(
            "({}) AND (({} > {}) OR (NOT hasProperty(\"{}\")))",
            query_specs.query.context("no query")?,
            EXPIRATION_TIMESTAMP_NAME,
            now_ts,
            EXPIRATION_TIMESTAMP_NAME,
        ));

        query_specs.enabled_features.push(icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string());
        if !query_specs.enabled_features.contains(&String::from("NUMERIC_SEARCH")) {
            query_specs.enabled_features.push("NUMERIC_SEARCH".to_string());
        }
        if !query_specs
            .enabled_features
            .contains(&String::from(icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE))
        {
            query_specs
                .enabled_features
                .push(icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string());
        }

        Ok((query_specs, score_spec))
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
        let field_name = match text_query.field() {
            MemoryField::CreatedTimestamp => CREATED_TIMESTAMP_NAME,
            MemoryField::EventTimestamp => EVENT_TIMESTAMP_NAME,
            MemoryField::ExpirationTimestamp => EXPIRATION_TIMESTAMP_NAME,
            MemoryField::Id => MEMORY_ID_NAME,
            MemoryField::Tags => TAG_NAME,
            _ => bail!("unsupported field for text search"),
        };

        let match_type = text_query.match_type();

        // Handle empty/None values: when no value is provided, generate
        // a query that checks for field existence (hasProperty).
        let (query, needs_has_property_feature) = match text_query.value.as_ref() {
            Some(text_query::Value::TimestampVal(timestamp)) => {
                let value = timestamp_to_i64(timestamp);
                (match_type.build_timestamp_query(field_name, value)?, false)
            }
            Some(text_query::Value::StringVal(text)) => {
                let value = text.to_string();
                if matches!(match_type, MatchType::Equal) && value.is_empty() {
                    // Empty string value with Equal match type: check for field existence
                    (format!("hasProperty(\"{field_name}\")"), true)
                } else {
                    (match_type.build_string_query(field_name, &value)?, false)
                }
            }
            None => {
                // No value provided: generate a hasProperty check for EQUAL match type,
                // otherwise return an error since comparison operators need a value.
                match match_type {
                    MatchType::Equal => (format!("hasProperty(\"{field_name}\")"), true),
                    _ => bail!("comparison operators require a value"),
                }
            }
        };

        let mut enabled_features = vec!["NUMERIC_SEARCH".to_string()];
        if needs_has_property_feature {
            enabled_features.push(icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string());
            enabled_features.push(icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string());
        }

        let mut search_spec = icing::SearchSpecProto {
            query: Some(query),
            enabled_features,
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            ..Default::default()
        };
        if !schema_name.is_empty() {
            search_spec.schema_type_filters.push(schema_name.to_string());
        }

        // Sort text search results by created_timestamp (descending, i.e. newest
        // first).
        let scoring_spec = icing::ScoringSpecProto {
            rank_by: Some(
                icing::scoring_spec_proto::ranking_strategy::Code::CreationTimestamp.into(),
            ),
            ..Default::default()
        };

        Ok((search_spec, Some(scoring_spec)))
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
            (SCHEMA_NAME, BLOB_ID_NAME)
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
        let (search_spec, scoring_spec) = self.build_text_query_specs(text_query, SCHEMA_NAME)?;
        let projection = Self::create_blob_id_projection(SCHEMA_NAME);
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

    pub fn delete_document(&mut self, blob_id: &BlobId) -> anyhow::Result<()> {
        let result =
            self.icing_search_engine.delete(NAMESPACE_NAME.as_bytes(), blob_id.as_bytes())?;
        if result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Failed to delete document with id {}: {:?}", blob_id, result.status);
        }
        Ok(())
    }

    pub fn delete_memories(&mut self, memory_ids: &[MemoryId]) -> anyhow::Result<()> {
        for memory_id in memory_ids {
            let view_ids = self.get_view_ids_by_memory_id(memory_id.clone())?;
            for view_id in view_ids {
                self.delete_document(&view_id)?;
            }
            self.delete_document(memory_id)?;
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
                MutationOperation::Reset => Ok(new_db.reset()?),
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

fn build_non_expired_query_str(property_name: &str, property_val: &str) -> String {
    let now_ts = timestamp_to_i64(&system_time_to_timestamp(SystemTime::now()));

    // A memory is considered not expired if its expiration timestamp is in the
    // future, or if it has no expiration timestamp set.
    let expiration_clause = format!(
        "({} > {}) OR (NOT hasProperty(\"{}\"))",
        EXPIRATION_TIMESTAMP_NAME, now_ts, EXPIRATION_TIMESTAMP_NAME
    );

    if property_val.is_empty() {
        // If no property value specified, filter just for non expired memories.
        expiration_clause
    } else {
        format!("({}:{}) AND ({})", property_name, property_val, expiration_clause)
    }
}

fn system_time_to_timestamp(system_time: SystemTime) -> prost_types::Timestamp {
    let (seconds, nanos) = match system_time.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => {
            let seconds = duration.as_secs() as i64;
            let nanos = duration.subsec_nanos() as i32;
            (seconds, nanos)
        }
        Err(e) => {
            let duration = e.duration();
            let seconds = -(duration.as_secs() as i64);
            let nanos = -(duration.subsec_nanos() as i32);
            (seconds, nanos)
        }
    };

    prost_types::Timestamp { seconds, nanos }
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
    fn icing_embedding_search_expired_memory_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let model_signature = "test_model".to_string();
        let embedding_values = vec![1.0, 0.0, 0.0]; // Common embedding for query

        // Create an expired memory
        let expired_memory_id = "expired_memory_embed".to_string();
        let expired_blob_id = "expired_blob_embed".to_string();
        let past_time = SystemTime::now() - std::time::Duration::from_secs(3600); // 1 hour ago
        let expiration_timestamp = Some(system_time_to_timestamp(past_time));

        let expired_memory = Memory {
            id: expired_memory_id.clone(),
            tags: vec!["embed_tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp,
            ..Default::default()
        };
        icing_database.add_memory(&expired_memory, expired_blob_id.clone())?;

        // Create a non-expired memory (expires in the future)
        let non_expired_memory_id = "non_expired_memory_embed".to_string();
        let non_expired_blob_id = "non_expired_blob_embed".to_string();
        let future_time = SystemTime::now() + std::time::Duration::from_secs(3600); // 1 hour in future
        let non_expired_timestamp = Some(system_time_to_timestamp(future_time));

        let non_expired_memory = Memory {
            id: non_expired_memory_id.clone(),
            tags: vec!["embed_tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "non_expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: non_expired_timestamp,
            ..Default::default()
        };
        icing_database.add_memory(&non_expired_memory, non_expired_blob_id.clone())?;

        // Create a never-expired memory (no expiration_timestamp)
        let never_expired_memory_id = "never_expired_memory_embed".to_string();
        let never_expired_blob_id = "never_expired_blob_embed".to_string();
        let never_expired_memory = Memory {
            id: never_expired_memory_id.clone(),
            tags: vec!["embed_tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "never_expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: None,
            ..Default::default()
        };
        icing_database.add_memory(&never_expired_memory, never_expired_blob_id.clone())?;

        // Query with an embedding that matches all three (if not for expiration)
        let embedding_query = SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
                embedding: vec![Embedding {
                    model_signature: model_signature.clone(),
                    values: embedding_values,
                }],
                ..Default::default()
            })),
        };

        let (results, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

        // Assert that just the non-expired and never-expired memories are in the search
        // results
        assert_that!(
            blob_ids,
            unordered_elements_are![eq(&non_expired_blob_id), eq(&never_expired_blob_id)]
        );

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
        let _ = db3.reset();

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

    #[gtest]
    fn icing_delete_memory_also_deletes_views_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;
        let memory_id = "memory_id".to_string();
        let blob_id = 12345.to_string();
        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![
                    LlmView {
                        id: "view1".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![1.0, 0.0, 0.0],
                        }),
                        ..Default::default()
                    },
                    LlmView {
                        id: "view2".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![0.0, 1.0, 0.0],
                        }),
                        ..Default::default()
                    },
                ],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory, blob_id.clone())?;
        let view_ids = icing_database.get_view_ids_by_memory_id(memory_id.clone());
        assert_that!(view_ids, ok(unordered_elements_are![eq(&"view1"), eq(&"view2")]));
        icing_database.delete_memories(&[memory_id.clone()])?;
        let view_ids = icing_database.get_view_ids_by_memory_id(memory_id);
        assert_that!(view_ids, ok(is_empty()));
        Ok(())
    }

    #[gtest]
    fn icing_update_memory_replaces_views_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;
        let memory_id = "memory_id_to_update".to_string();
        let blob_id1 = "blob_id_1".to_string();

        // First, add a memory with two views.
        let memory1 = Memory {
            id: memory_id.clone(),
            tags: vec!["tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![
                    LlmView {
                        id: "view1".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![1.0, 0.0, 0.0],
                        }),
                        ..Default::default()
                    },
                    LlmView {
                        id: "view2".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![0.0, 1.0, 0.0],
                        }),
                        ..Default::default()
                    },
                ],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory1, blob_id1)?;

        // Check that the views were added.
        let view_ids1 = icing_database.get_view_ids_by_memory_id(memory_id.clone())?;
        assert_that!(view_ids1, unordered_elements_are![eq(&"view1"), eq(&"view2")]);

        // Now, "update" the memory by adding a new memory with the same ID but
        // different views.
        let blob_id2 = "blob_id_2".to_string();
        let memory2 = Memory {
            id: memory_id.clone(),
            tags: vec!["tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "view3".to_string(), // New view
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![0.0, 0.0, 1.0],
                    }),
                    ..Default::default()
                }],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory2, blob_id2)?;

        // Check that the old views are gone and only the new one exists.
        let view_ids2 = icing_database.get_view_ids_by_memory_id(memory_id.clone())?;
        assert_that!(view_ids2, unordered_elements_are![eq(&"view3")]);

        // Update again, this time with no views.
        let blob_id3 = "blob_id_3".to_string();
        let memory3 =
            Memory { id: memory_id.clone(), tags: vec!["tag".to_string()], ..Default::default() };
        icing_database.add_memory(&memory3, blob_id3)?;

        // Check that all views are gone.
        let view_ids3 = icing_database.get_view_ids_by_memory_id(memory_id)?;
        assert_that!(view_ids3, is_empty());

        Ok(())
    }

    #[gtest]
    fn icing_search_with_view_scores_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let memory_id = "memory_id_view_scores".to_string();
        let blob_id = "blob_id_view_scores".to_string();
        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["tag".to_string()],
            views: Some(LlmViews {
                llm_views: vec![
                    LlmView {
                        id: "view1".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![1.0, 0.0, 0.0],
                        }),
                        ..Default::default()
                    },
                    LlmView {
                        id: "view2".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![0.0, 1.0, 0.0],
                        }),
                        ..Default::default()
                    },
                ],
            }),
            ..Default::default()
        };
        icing_database.add_memory(&memory, blob_id.clone())?;

        let embedding_query = SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
                embedding: vec![Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![0.7, 0.3, 0.0],
                }],
                ..Default::default()
            })),
        };

        let (results, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
        assert_that!(results.items, len(eq(1)));
        let result = &results.items[0];
        assert_eq!(result.blob_id, blob_id);
        assert_that!(&result.view_ids, elements_are![eq("view1"), eq("view2")]);
        assert_that!(&result.view_scores, elements_are![eq(&0.7), eq(&0.3)]);
        assert_eq!(result.score, 1.0);

        Ok(())
    }

    #[gtest]
    fn icing_get_memory_by_id_with_expiration_timestamp_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        let memory_id = "expired_memory_id".to_string();
        let blob_id = "expired_blob_id".to_string();

        // Create a timestamp in the past (e.g., 1 hour ago)
        let past_time = SystemTime::now() - std::time::Duration::from_secs(3600);
        let expiration_timestamp = Some(system_time_to_timestamp(past_time));

        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["expired".to_string()],
            expiration_timestamp,
            ..Default::default()
        };
        icing_database.add_memory(&memory, blob_id.clone())?;

        // Verify the memory is actually stored in the database without considering
        // expiration.
        let search_spec_for_existence = icing::SearchSpecProto {
            query: Some(memory_id.to_string()),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            type_property_filters: vec![IcingMetaDatabase::create_search_filter(
                SCHEMA_NAME,
                MEMORY_ID_NAME,
            )],
            ..Default::default()
        };

        let result_spec_for_existence = icing::ResultSpecProto {
            num_per_page: Some(1),
            type_property_masks: vec![IcingMetaDatabase::create_blob_id_projection(SCHEMA_NAME)],
            ..Default::default()
        };
        let search_result_for_existence = icing_database.icing_search_engine.search(
            &search_spec_for_existence,
            &icing::get_default_scoring_spec(),
            &result_spec_for_existence,
        );

        assert_that!(search_result_for_existence.as_ref().unwrap().results, len(eq(1)));
        assert_that!(
            IcingMetaDatabase::extract_blob_id_from_doc(
                &search_result_for_existence.unwrap().results[0]
            ),
            eq(&Some(blob_id.clone()))
        );

        // Try to retrieve the memory using the public API, it should not be found
        // because it's expired
        expect_that!(icing_database.get_blob_id_by_memory_id(memory_id)?, eq(&None));

        Ok(())
    }

    #[gtest]
    fn icing_get_memories_by_tag_with_expiration_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;
        let common_tag = "test_tag".to_string();

        // Memory 1: Expired
        let memory_id_expired = "memory_expired".to_string();
        let blob_id_expired = "blob_expired".to_string();
        let past_time = SystemTime::now() - std::time::Duration::from_secs(3600); // 1 hour ago
        let memory_expired = Memory {
            id: memory_id_expired.clone(),
            tags: vec![common_tag.clone()],
            expiration_timestamp: Some(system_time_to_timestamp(past_time)),
            ..Default::default()
        };
        icing_database.add_memory(&memory_expired, blob_id_expired.clone())?;

        // Memory 2: Future expiration
        let memory_id_future = "memory_future".to_string();
        let blob_id_future = "blob_future".to_string();
        let future_time = SystemTime::now() + std::time::Duration::from_secs(3600); // 1 hour from now
        let memory_future = Memory {
            id: memory_id_future.clone(),
            tags: vec![common_tag.clone()],
            expiration_timestamp: Some(system_time_to_timestamp(future_time)),
            ..Default::default()
        };
        icing_database.add_memory(&memory_future, blob_id_future.clone())?;

        // Memory 3: No expiration
        let memory_id_no_expiry = "memory_no_expiry".to_string();
        let blob_id_no_expiry = "blob_no_expiry".to_string();
        let memory_no_expiry = Memory {
            id: memory_id_no_expiry.clone(),
            tags: vec![common_tag.clone()],
            expiration_timestamp: None,
            ..Default::default()
        };
        icing_database.add_memory(&memory_no_expiry, blob_id_no_expiry.clone())?;

        // Retrieve memories by tag
        let (results, _) = icing_database.get_memories_by_tag(&common_tag, 10, PageToken::Start)?;

        // Assert that only non-expired memories are returned
        assert_that!(results, unordered_elements_are![eq(&blob_id_future), eq(&blob_id_no_expiry)]);

        Ok(())
    }

    #[gtest]
    fn build_text_query_specs_with_no_value_test() -> anyhow::Result<()> {
        let icing_database = IcingMetaDatabase::new(tempdir())?;

        // Test with None value and EQUAL match type - should generate hasProperty query
        let text_query = TextQuery {
            match_type: MatchType::Equal.into(),
            field: MemoryField::Tags.into(),
            value: None,
        };

        let (search_spec, _) = icing_database.build_text_query_specs(&text_query, SCHEMA_NAME)?;

        // Verify query uses hasProperty
        expect_that!(search_spec.query.as_ref().unwrap(), eq(&"hasProperty(\"tag\")".to_string()));

        // Verify enabled features include HAS_PROPERTY_FUNCTION_FEATURE
        expect_that!(
            search_spec.enabled_features,
            contains(eq(&icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string()))
        );
        expect_that!(
            search_spec.enabled_features,
            contains(eq(&icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()))
        );

        Ok(())
    }

    #[gtest]
    fn build_text_query_specs_with_empty_string_value_test() -> anyhow::Result<()> {
        let icing_database = IcingMetaDatabase::new(tempdir())?;

        // Test with empty string value and EQUAL match type - should generate
        // hasProperty query
        let text_query = TextQuery {
            match_type: MatchType::Equal.into(),
            field: MemoryField::Id.into(),
            value: Some(text_query::Value::StringVal("".to_string())),
        };

        let (search_spec, _) = icing_database.build_text_query_specs(&text_query, SCHEMA_NAME)?;

        // Verify query uses hasProperty
        expect_that!(
            search_spec.query.as_ref().unwrap(),
            eq(&"hasProperty(\"memoryId\")".to_string())
        );

        // Verify enabled features include HAS_PROPERTY_FUNCTION_FEATURE
        expect_that!(
            search_spec.enabled_features,
            contains(eq(&icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string()))
        );

        Ok(())
    }

    #[gtest]
    fn build_text_query_specs_comparison_with_no_value_fails_test() -> anyhow::Result<()> {
        let icing_database = IcingMetaDatabase::new(tempdir())?;

        // Test with None value and GTE match type - should fail
        let text_query = TextQuery {
            match_type: MatchType::Gte.into(),
            field: MemoryField::CreatedTimestamp.into(),
            value: None,
        };

        let result = icing_database.build_text_query_specs(&text_query, SCHEMA_NAME);
        expect_that!(result.is_err(), eq(true));

        Ok(())
    }

    #[gtest]
    fn build_text_query_specs_with_string_value_test() -> anyhow::Result<()> {
        let icing_database = IcingMetaDatabase::new(tempdir())?;

        // Test with a non-empty string value - should work as before
        let text_query = TextQuery {
            match_type: MatchType::Equal.into(),
            field: MemoryField::Tags.into(),
            value: Some(text_query::Value::StringVal("my_tag".to_string())),
        };

        let (search_spec, _) = icing_database.build_text_query_specs(&text_query, SCHEMA_NAME)?;

        // Verify query uses standard term search
        expect_that!(search_spec.query.as_ref().unwrap(), eq(&"(tag:my_tag)".to_string()));

        // Verify HAS_PROPERTY_FUNCTION_FEATURE is NOT included (not needed)
        expect_that!(
            search_spec.enabled_features,
            not(contains(eq(&icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string())))
        );

        Ok(())
    }

    /// Test that delete_memories correctly deletes a memory by MemoryId and
    /// that get_blob_id_by_memory_id returns None after deletion.
    /// This verifies the fix for the bug where cache deletion was passing
    /// MemoryId instead of BlobId.
    #[gtest]
    fn delete_memories_uses_correct_id_types_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        // Add a memory with a distinct memory_id and blob_id
        let memory_id = "test_memory_id".to_string();
        let blob_id = "test_blob_id_12345".to_string();
        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["test_tag".to_string()],
            ..Default::default()
        };
        icing_database.add_memory(&memory, blob_id.clone())?;

        // Verify the memory was added and blob_id can be looked up
        expect_that!(
            icing_database.get_blob_id_by_memory_id(memory_id.clone())?,
            eq(&Some(blob_id.clone()))
        );

        // Verify we can find this memory by tag search
        let (results, _) = icing_database.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, contains(eq(&blob_id)));

        // Now delete the memory using memory_id (not blob_id!)
        icing_database.delete_memories(&[memory_id.clone()])?;

        // After deletion, get_blob_id_by_memory_id should return None.
        // This is the key lookup that DatabaseWithCache uses to get the
        // correct BlobId for cache deletion.
        expect_that!(icing_database.get_blob_id_by_memory_id(memory_id)?, eq(&None));

        // Verify the memory is no longer findable by tag search
        let (results, _) = icing_database.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, is_empty());

        Ok(())
    }

    /// Test that text_search returns results sorted by created_timestamp
    /// in descending order (newest first).
    #[gtest]
    fn text_search_sorts_by_created_timestamp_test() -> anyhow::Result<()> {
        let mut icing_database = IcingMetaDatabase::new(tempdir())?;

        // Add memories with different created_timestamps, inserted in non-sorted order
        let memory_old = Memory {
            id: "memory_old".to_string(),
            tags: vec!["sort_test".to_string()],
            created_timestamp: Some(prost_types::Timestamp { seconds: 1000, nanos: 0 }),
            ..Default::default()
        };
        icing_database.add_memory(&memory_old, "blob_old".to_string())?;

        let memory_new = Memory {
            id: "memory_new".to_string(),
            tags: vec!["sort_test".to_string()],
            created_timestamp: Some(prost_types::Timestamp { seconds: 3000, nanos: 0 }),
            ..Default::default()
        };
        icing_database.add_memory(&memory_new, "blob_new".to_string())?;

        let memory_mid = Memory {
            id: "memory_mid".to_string(),
            tags: vec!["sort_test".to_string()],
            created_timestamp: Some(prost_types::Timestamp { seconds: 2000, nanos: 0 }),
            ..Default::default()
        };
        icing_database.add_memory(&memory_mid, "blob_mid".to_string())?;

        // Search for all memories with tag "sort_test"
        let text_query = TextQuery {
            field: MemoryField::Tags as i32,
            match_type: MatchType::Equal as i32,
            value: Some(text_query::Value::StringVal("sort_test".to_string())),
        };
        let (results, _) = icing_database.text_search(&text_query, 10, PageToken::Start)?;

        // Results should be sorted by created_timestamp descending (newest first)
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        expect_that!(blob_ids.len(), eq(3));
        // Newest (3000) first, then middle (2000), then oldest (1000)
        expect_that!(blob_ids, elements_are![eq("blob_new"), eq("blob_mid"), eq("blob_old")]);

        Ok(())
    }
}
