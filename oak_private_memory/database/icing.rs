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

use anyhow::{Context, bail, ensure};
use external_db_client::BlobId;
use icing::{DocumentProto, IcingGroundTruthFilesHelper};
use log::{debug, error, info};
use prost::Message;
use rand::Rng;
use sealed_memory_rust_proto::{
    oak::private_memory::{
        EmbeddingQuery, LlmView, MatchType, QueryClauses, QueryOperator, SearchMemoryQuery,
        TextQuery, search_memories_filter, search_memory_query, text_query,
    },
    prelude::v1::*,
};

use crate::{MemoryId, ViewId, clock::system_time_to_timestamp};

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
const NAME_NAME: &str = "name";
const MEMORY_ID_NAME: &str = "memoryId";
const BLOB_ID_NAME: &str = "blobId";
const EMBEDDING_NAME: &str = "embedding";
const CREATED_TIMESTAMP_NAME: &str = "createdTimestamp";
const EVENT_TIMESTAMP_NAME: &str = "eventTimestamp";
const EXPIRATION_TIMESTAMP_NAME: &str = "expirationTimestamp";

const LLM_VIEW_SCHEMA_NAME: &str = "LlmView";
const VIEW_ID_NAME: &str = "viewId";
const VIEW_TYPE_NAME: &str = "viewType";

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
        let name: &String = &memory.name;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let document_builder = icing::create_document_builder();
        let document_builder = document_builder
            .set_key(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes())
            .set_schema(SCHEMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()]);

        if !name.is_empty() {
            document_builder.add_string_property(NAME_NAME.as_bytes(), &[name.as_bytes()]);
        }

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
        let view_type: &String = &view.r#type;
        let name = &memory.name;
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
            .add_string_property(VIEW_TYPE_NAME.as_bytes(), &[view_type.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()])
            .add_vector_property(EMBEDDING_NAME.as_bytes(), &embeddings);

        if !name.is_empty() {
            document_builder.add_string_property(NAME_NAME.as_bytes(), &[name.as_bytes()]);
        }

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
                    .set_name(NAME_NAME.as_bytes())
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
                    )
                    .set_scorable_type(
                        icing::property_config_proto::scorable_type::Code::Enabled.into(),
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
                    )
                    .set_scorable_type(
                        icing::property_config_proto::scorable_type::Code::Enabled.into(),
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
                    .set_name(NAME_NAME.as_bytes())
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
                    .set_name(VIEW_TYPE_NAME.as_bytes())
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
        page_size: i32,
        page_token: PageToken,
    ) -> anyhow::Result<(Vec<BlobId>, PageToken)> {
        if page_token == PageToken::Invalid {
            bail!("Invalid page token provided");
        }

        let query = SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
                field: MemoryField::Tags as i32,
                match_type: MatchType::Equal as i32,
                value: Some(text_query::Value::StringVal(tag.to_string())),
            })),
        };
        let (search_spec, scoring_spec) =
            self.build_query_specs_filtering_expired_memories(&query, SCHEMA_NAME)?;
        let projection = Self::create_blob_id_projection(SCHEMA_NAME);
        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &scoring_spec.unwrap_or_default(),
            page_size,
            page_token,
            projection,
        )?;
        let blob_ids = Self::extract_blob_ids_from_search_result(search_result);
        if blob_ids.is_empty() {
            return Ok((blob_ids, PageToken::Start));
        }
        Ok((blob_ids, next_page_token))
    }

    pub fn get_memory_by_name(&self, name: &str) -> anyhow::Result<Option<BlobId>> {
        let query_str = build_non_expired_query_str(NAME_NAME, name);

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
            num_per_page: Some(2), // We expect at most one result, but set to two to detect errors.
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
            bail!("Icing search failed: {:?}", search_result.status);
        }

        if search_result.results.is_empty() {
            return Ok(None);
        }

        if search_result.results.len() > 1 {
            bail!("Two memories with the same name found: {:?}", search_result.results)
        }
        Ok(search_result.results.first().and_then(Self::extract_blob_id_from_doc))
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
        if ids.is_empty() { Ok((ids, PageToken::Start)) } else { Ok((ids, next_page_token)) }
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

        // For text-only queries, Icing returns results already sorted by
        // CreationTimestamp descending. We build results directly from the
        // ordered output to preserve this ordering (a HashMap would lose it).
        if !search_views {
            let (search_result, next_page_token) = self.execute_search(
                &search_spec,
                &scoring_spec,
                page_size,
                page_token,
                projection.clone(),
            )?;
            let mut search_result_ids = SearchResultIds::default();
            for result in &search_result.results {
                if let Some(blob_id) = Self::extract_blob_id_from_doc(result) {
                    let score = result.score.map(|s| s as f32).unwrap_or(0.0);
                    search_result_ids.items.push(SearchResultId {
                        blob_id,
                        score,
                        view_ids: Vec::new(),
                        view_scores: Vec::new(),
                    });
                }
            }
            return Ok((search_result_ids, next_page_token));
        }

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
        let mut id_maps: HashMap<BlobId, Vec<(ViewId, f32)>> = HashMap::new();
        loop {
            let (search_result, next_page_token) = self.execute_search(
                &search_spec,
                &scoring_spec,
                1,
                page_token,
                projection.clone(),
            )?;
            page_token = next_page_token;

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

        // Check upfront if any clause involves embedding search.
        // If so, use embedding-based scoring; otherwise use text-based scoring.
        let has_embedding_search = clauses.clauses.iter().any(Self::is_embedding_search);

        let mut sub_queries = Vec::new();
        let mut embedding_vectors = Vec::new();
        let mut metric_type = None;
        for clause in &clauses.clauses {
            let (spec, _) = self.build_query_specs(clause, schema_name)?;
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

        // Use embedding scoring if any clause involves embedding search,
        // otherwise use text-based CreationTimestamp scoring.
        let score_spec = if has_embedding_search {
            Some(self.build_scoring_spec())
        } else {
            Some(icing::ScoringSpecProto {
                rank_by: Some(
                    icing::scoring_spec_proto::ranking_strategy::Code::CreationTimestamp.into(),
                ),
                ..Default::default()
            })
        };

        Ok((search_spec, score_spec))
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

    // =========================================================================
    // Search API v2 implementation
    // =========================================================================

    /// Entry point for the Search API v2.
    ///
    /// Translates a `SearchMemoriesRequest` into Icing search/scoring specs,
    /// executes the query, and returns matching memory blob IDs with scores.
    pub fn search_memories(
        &self,
        request: &SearchMemoriesRequest,
    ) -> anyhow::Result<(SearchResultIds, PageToken)> {
        let filter = request.filter.as_ref().context("SearchMemoriesRequest.filter is required")?;

        // Build the Icing search spec from the filter tree.
        let search_spec = self.build_search_memories_filter(filter, SCHEMA_NAME)?;

        let scoring_spec = Self::build_search_memories_sort_mode(&request.sort)?;

        let page_size = request.page_size;

        let page_token = PageToken::try_from(request.page_token.clone())
            .map_err(|e| anyhow::anyhow!("invalid page token: {}", e))?;

        let projection = icing::TypePropertyMask {
            schema_type: Some(SCHEMA_NAME.to_string()),
            paths: vec![BLOB_ID_NAME.to_string()],
        };

        let (search_result, next_page_token) =
            self.execute_search(&search_spec, &scoring_spec, page_size, page_token, projection)?;

        let mut search_result_ids = SearchResultIds::default();
        for result in &search_result.results {
            if let Some(blob_id) = Self::extract_blob_id_from_doc(result) {
                let score = result.score.map(|s| s as f32).unwrap_or(0.0);
                search_result_ids.items.push(SearchResultId {
                    blob_id,
                    score,
                    view_ids: Vec::new(),
                    view_scores: Vec::new(),
                });
            }
        }

        Ok((search_result_ids, next_page_token))
    }

    /// Translate `SearchMemoriesSort` into an Icing `ScoringSpecProto`.
    ///
    /// All sort modes use a single Icing query with `AdvancedScoringExpression`
    /// and `getScorableProperty()` to read int64 property values at scoring
    /// time. Memories **with** the sorted field always receive a higher score
    /// than memories without it, so missing-field items naturally sort last.
    fn build_search_memories_sort_mode(
        sorts: &[SearchMemoriesSort],
    ) -> anyhow::Result<icing::ScoringSpecProto> {
        use sealed_memory_rust_proto::oak::private_memory::search_memories_sort::Sort;

        if sorts.is_empty() {
            // Default: created_timestamp descending.
            return Ok(icing::ScoringSpecProto {
                rank_by: Some(
                    icing::scoring_spec_proto::ranking_strategy::Code::CreationTimestamp.into(),
                ),
                ..Default::default()
            });
        }

        ensure!(sorts.len() == 1, "Only one sort field is supported for now");
        // Use only the first sort field (Icing supports a single ranking).
        let sort = sorts[0].sort.as_ref().context("SearchMemoriesSort.sort is required")?;
        match sort {
            Sort::CreatedTimestampSort(ts) => {
                if ts.order() == SortOrder::OrderAscending {
                    Ok(icing::ScoringSpecProto {
                        rank_by: Some(
                            icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
                        ),
                        advanced_scoring_expression: Some(
                            "-1 * this.creationTimestamp()".to_string(),
                        ),
                        ..Default::default()
                    })
                } else {
                    Ok(icing::ScoringSpecProto {
                        rank_by: Some(
                            icing::scoring_spec_proto::ranking_strategy::Code::CreationTimestamp
                                .into(),
                        ),
                        ..Default::default()
                    })
                }
            }
            Sort::EventTimestampSort(ts) => Ok(Self::build_scorable_property_sort(
                SCHEMA_NAME,
                EVENT_TIMESTAMP_NAME,
                ts.order() == SortOrder::OrderAscending,
            )),
            Sort::ExpirationTimestampSort(ts) => Ok(Self::build_scorable_property_sort(
                SCHEMA_NAME,
                EXPIRATION_TIMESTAMP_NAME,
                ts.order() == SortOrder::OrderAscending,
            )),
            Sort::EmbeddingSort(_) => {
                bail!("embedding sort is not yet supported in this CL")
            }
        }
    }

    /// Build a `ScoringSpecProto` that sorts by a scorable int64 property.
    ///
    /// Uses `getScorableProperty(schema, property)` as the advanced scoring
    /// expression. Memories without the property receive a sentinel score
    /// via `maxOrDefault` so they always rank last.
    ///
    /// - Descending (default): higher property value → higher score → ranked
    ///   first. Missing items get score -1 (via `maxOrDefault`), ranked last.
    /// - Ascending: lower values come first via `order_by = ASC`. Missing items
    ///   get score 1e18 (via `maxOrDefault`), ranked last.
    fn build_scorable_property_sort(
        schema_name: &str,
        property_name: &str,
        ascending: bool,
    ) -> icing::ScoringSpecProto {
        // `getScorableProperty` returns an empty list when the property is
        // absent, so `maxOrDefault(list, default)` lets us assign a sentinel
        // score that pushes missing items to the end regardless of direction.
        //
        // `this.creationTimestamp() / 1e18` is a tiebreaker that ensures
        // deterministic ordering when multiple documents share the same
        // property value (or are all missing it). Dividing by 1e18 keeps
        // the tiebreaker magnitude negligible compared to timestamp values
        // (~1e9–1e12), so it only affects ordering among ties.
        let (default_val, order_by) = if ascending {
            // Missing → huge value → sorted last in ASC.
            ("1e18", Some(icing::scoring_spec_proto::order::Code::Asc.into()))
        } else {
            // Missing → -1 → sorted last in DESC.
            ("-1", None)
        };
        let scorable_property =
            format!("getScorableProperty(\"{schema_name}\", \"{property_name}\")");
        let primary_score = format!("maxOrDefault({scorable_property}, {default_val})");
        let tiebreaker = "this.creationTimestamp() / 1e18";
        let expression = format!("{primary_score} + {tiebreaker}");
        icing::ScoringSpecProto {
            rank_by: Some(
                icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
            ),
            advanced_scoring_expression: Some(expression),
            order_by,
            scoring_feature_types_enabled: vec![
                icing::ScoringFeatureType::ScorablePropertyRanking.into(),
            ],
            // Map the schema name used in getScorableProperty() to the actual
            // Icing schema type. Required for the scoring visitor to resolve
            // the schema type reference.
            schema_type_alias_map_protos: vec![icing::SchemaTypeAliasMapProto {
                alias_schema_type: Some(schema_name.to_string()),
                schema_types: vec![schema_name.to_string()],
            }],
            ..Default::default()
        }
    }

    /// Recursively translate a `SearchMemoriesFilter` into an Icing
    /// `SearchSpecProto`.
    fn build_search_memories_filter(
        &self,
        filter: &SearchMemoriesFilter,
        schema_name: &str,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        use search_memories_filter::Value;
        let value = filter.value.as_ref().context("SearchMemoriesFilter.value is required")?;
        match value {
            Value::IdFilter(f) => {
                self.build_string_filter_spec(MEMORY_ID_NAME, &f.value, schema_name)
            }
            Value::NameFilter(f) => self.build_string_filter_spec(NAME_NAME, &f.value, schema_name),
            Value::TagsFilter(f) => self.build_string_filter_spec(TAG_NAME, &f.value, schema_name),
            Value::CreatedTimestampFilter(f) => {
                self.build_time_filter_spec(CREATED_TIMESTAMP_NAME, f, schema_name)
            }
            Value::EventTimestampFilter(f) => {
                self.build_time_filter_spec(EVENT_TIMESTAMP_NAME, f, schema_name)
            }
            Value::ExpirationTimestampFilter(f) => {
                self.build_time_filter_spec(EXPIRATION_TIMESTAMP_NAME, f, schema_name)
            }
            Value::EmbeddingFilter(f) => self.build_embedding_filter_spec(f),
            Value::AndOperator(filters) => {
                self.build_composite_filter(&filters.filters, "AND", schema_name)
            }
            Value::OrOperator(filters) => {
                self.build_composite_filter(&filters.filters, "OR", schema_name)
            }
            Value::NotOperator(inner) => {
                let mut child = self.build_search_memories_filter(inner, schema_name)?;
                let child_query = child.query.take().context("child filter produced no query")?;
                child.query = Some(format!("NOT ({child_query})"));
                Ok(child)
            }
        }
    }

    /// Combine multiple sub-filters with a boolean operator (AND / OR).
    fn build_composite_filter(
        &self,
        filters: &[SearchMemoriesFilter],
        operator: &str,
        schema_name: &str,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        ensure!(!filters.is_empty(), "composite filter must have at least one child");
        let mut sub_queries = Vec::new();
        let mut merged_features: Vec<String> = Vec::new();
        let mut merged_spec = icing::SearchSpecProto::default();

        for child_filter in filters {
            let child = self.build_search_memories_filter(child_filter, schema_name)?;
            if let Some(q) = child.query {
                sub_queries.push(q);
            }
            for feat in child.enabled_features {
                if !merged_features.contains(&feat) {
                    merged_features.push(feat);
                }
            }
            // Inherit schema_type_filters and term_match_type from children.
            if merged_spec.term_match_type.is_none() {
                merged_spec.term_match_type = child.term_match_type;
            }
            for st in child.schema_type_filters {
                if !merged_spec.schema_type_filters.contains(&st) {
                    merged_spec.schema_type_filters.push(st);
                }
            }
        }

        let combined = sub_queries
            .iter()
            .map(|q| format!("({q})"))
            .collect::<Vec<_>>()
            .join(&format!(" {operator} "));
        merged_spec.query = Some(combined);
        merged_spec.enabled_features = merged_features;
        Ok(merged_spec)
    }

    /// Build an Icing `SearchSpecProto` for an exact-match string property
    /// filter.
    fn build_string_filter_spec(
        &self,
        field_name: &str,
        value: &str,
        schema_name: &str,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        let query_string = format!("({field_name}:{value})");
        let mut search_spec = icing::SearchSpecProto {
            query: Some(query_string),
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
        Ok(search_spec)
    }

    /// Build an Icing `SearchSpecProto` for an embedding filter.
    fn build_embedding_filter_spec(
        &self,
        filter: &EmbeddingFilter,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        let embedding: &Embedding =
            filter.embedding.as_ref().context("EmbeddingFilter.embedding is required")?;
        let minimum_score: f32 = filter.minimum_score;
        let view_type: &str = &filter.view_type;

        // Search the first embedding property, specified by `EMBEDDING_NAME`.
        // Since we have only one embedding property, this is the one to go.
        let mut query_string =
            format!("semanticSearch(getEmbeddingParameter(0), {minimum_score}, 1)");
        if !view_type.is_empty() {
            query_string = format!("({}:{}) AND {}", VIEW_TYPE_NAME, view_type, query_string);
        }

        let search_spec = icing::SearchSpecProto {
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            embedding_query_metric_type: Some(
                icing::search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
            ),
            embedding_query_vectors: vec![icing::create_vector_proto(
                embedding.model_signature.as_str(),
                &embedding.values,
            )],
            query: Some(query_string),
            enabled_features: vec![icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()],
            schema_type_filters: vec![LLM_VIEW_SCHEMA_NAME.to_string()],
            ..Default::default()
        };
        Ok(search_spec)
    }

    /// Build an Icing `SearchSpecProto` for a timestamp comparison filter.
    fn build_time_filter_spec(
        &self,
        field_name: &str,
        filter: &TimeFilter,
        schema_name: &str,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        let timestamp = filter.value.as_ref().context("TimeFilter.value is required")?;
        let value = timestamp_to_i64(timestamp);
        let op = match filter.comparison() {
            ComparisonType::Unspecified | ComparisonType::Eq => "==",
            ComparisonType::Gte => ">=",
            ComparisonType::Lte => "<=",
            ComparisonType::Lt => "<",
            ComparisonType::Gt => ">",
        };
        let query_string = format!("({field_name} {op} {value})");
        let mut search_spec = icing::SearchSpecProto {
            query: Some(query_string),
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
        Ok(search_spec)
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

    /// Returns (memory_count, llm_view_count) across all documents in the
    /// database, including expired ones.
    pub fn get_document_counts(&self) -> anyhow::Result<(i64, i64)> {
        let memory_count = self.count_documents_by_schema(SCHEMA_NAME)? as i64;
        let llm_view_count = self.count_documents_by_schema(LLM_VIEW_SCHEMA_NAME)? as i64;
        Ok((memory_count, llm_view_count))
    }

    fn count_documents_by_schema(&self, schema_name: &str) -> anyhow::Result<usize> {
        let mut count: usize = 0;
        let mut page_token = PageToken::Start;
        loop {
            let search_spec = icing::SearchSpecProto {
                query: Some(format!("hasProperty(\"{}\")", BLOB_ID_NAME)),
                enabled_features: vec![
                    icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string(),
                    icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
                ],
                term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
                schema_type_filters: vec![schema_name.to_string()],
                ..Default::default()
            };
            // Use an empty projection — we only need the count, not the data.
            let result_spec = icing::ResultSpecProto {
                num_per_page: Some(1000),
                type_property_masks: vec![icing::TypePropertyMask {
                    schema_type: Some(schema_name.to_string()),
                    paths: vec![],
                }],
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
                bail!("Icing count failed: {:?}", search_result.status);
            }

            count += search_result.results.len();

            let next_page_token =
                search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
            if next_page_token == PageToken::Start {
                break;
            }
            page_token = next_page_token;
        }
        Ok(count)
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

    // =========================================================================
    // Test helpers
    // =========================================================================

    fn tempdir() -> IcingTempDir {
        IcingTempDir::new("icing-test-")
    }

    /// Creates a single `LlmView` with a "test_model" embedding.
    fn llm_view(id: &str, values: &[f32]) -> LlmView {
        LlmView {
            id: id.to_string(),
            embedding: Some(Embedding {
                model_signature: "test_model".to_string(),
                values: values.to_vec(),
            }),
            ..Default::default()
        }
    }

    /// Creates a tagged memory with a single embedding view.
    fn mem_with_view(id: &str, tags: &[&str], view_id: &str, values: &[f32]) -> Memory {
        Memory {
            id: id.into(),
            tags: tags.iter().map(|t| t.to_string()).collect(),
            views: Some(LlmViews { llm_views: vec![llm_view(view_id, values)] }),
            ..Default::default()
        }
    }

    /// Creates a tagged memory with multiple views.
    fn mem_with_views(id: &str, tags: &[&str], views: Vec<LlmView>) -> Memory {
        Memory {
            id: id.into(),
            tags: tags.iter().map(|t| t.to_string()).collect(),
            views: Some(LlmViews { llm_views: views }),
            ..Default::default()
        }
    }

    /// Builds an embedding search query with "test_model".
    fn embedding_query(values: &[f32]) -> SearchMemoryQuery {
        SearchMemoryQuery {
            clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
                embedding: vec![Embedding {
                    model_signature: "test_model".to_string(),
                    values: values.to_vec(),
                }],
                ..Default::default()
            })),
        }
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

    fn ts(seconds: i64) -> prost_types::Timestamp {
        prost_types::Timestamp { seconds, nanos: 0 }
    }

    // =========================================================================
    // Tests
    // =========================================================================

    #[gtest]
    fn basic_icing_search_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let blob_id = 12345.to_string();
        db.add_memory(
            &Memory { id: "Thisisanid".into(), tags: vec!["the_tag".into()], ..Default::default() },
            blob_id.clone(),
        )?;
        let blob_id2 = 12346.to_string();
        db.add_memory(
            &Memory {
                id: "Thisisanid2".into(),
                tags: vec!["the_tag".into()],
                ..Default::default()
            },
            blob_id2.clone(),
        )?;

        let (result, _) = db.get_memories_by_tag("the_tag", 10, PageToken::Start)?;
        assert_that!(result, unordered_elements_are![eq(&blob_id), eq(&blob_id2)]);
        Ok(())
    }

    #[gtest]
    fn icing_import_export_test() -> anyhow::Result<()> {
        let base_dir = tempdir();
        let base_dir_string = base_dir.as_str().to_string();
        let mut db = IcingMetaDatabase::new(base_dir)?;

        let memory_id1 = "memory_id_export_1".to_string();
        let blob_id1 = 654321.to_string();
        db.add_memory(
            &Memory {
                id: memory_id1.clone(),
                tags: vec!["export_tag".into()],
                ..Default::default()
            },
            blob_id1.clone(),
        )?;

        let exported_data = db.export()?.encode_to_vec();
        drop(db);
        expect_false!(std::path::Path::new(base_dir_string.as_str()).exists());

        let imported_db = IcingMetaDatabase::import(tempdir(), exported_data.as_slice())
            .expect("failed to import");

        expect_that!(
            imported_db.get_blob_id_by_memory_id(memory_id1)?,
            eq(&Some(blob_id1.clone()))
        );
        let (result, _) = imported_db.get_memories_by_tag("export_tag", 10, PageToken::Start)?;
        assert_that!(result, unordered_elements_are![eq(&blob_id1)]);
        Ok(())
    }

    #[gtest]
    fn icing_get_blob_id_by_memory_id_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let (mid1, bid1) = ("memory_id_1".to_string(), 54321.to_string());
        db.add_memory(
            &Memory { id: mid1.clone(), tags: vec!["tag1".into()], ..Default::default() },
            bid1.clone(),
        )?;

        let (mid2, bid2) = ("memory_id_2".to_string(), 54322.to_string());
        db.add_memory(
            &Memory { id: mid2.clone(), tags: vec!["tag2".into()], ..Default::default() },
            bid2.clone(),
        )?;

        expect_that!(db.get_blob_id_by_memory_id(mid1)?, eq(&Some(bid1)));
        expect_that!(db.get_blob_id_by_memory_id(mid2)?, eq(&Some(bid2)));
        expect_that!(db.get_blob_id_by_memory_id("non_existent_id".into())?, eq(&None));
        Ok(())
    }

    #[gtest]
    fn icing_embedding_search_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let bid1 = 98765.to_string();
        db.add_memory(
            &mem_with_view("memory_embed_1", &["embed_tag"], "view1", &[1.0, 0.0, 0.0]),
            bid1.clone(),
        )?;

        let bid2 = 98766.to_string();
        db.add_memory(
            &mem_with_view("memory_embed_2", &["embed_tag"], "view2", &[0.0, 1.0, 0.0]),
            bid2.clone(),
        )?;

        let query = embedding_query(&[0.9, 0.1, 0.0]);

        // Query embedding close to embedding1
        let (results, _) = db.search(&query, 10, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
        assert_that!(blob_ids, elements_are![eq(&bid1), eq(&bid2)]);
        assert_that!(scores, elements_are![eq(&0.9), eq(&0.1)]);

        // With limit=1, only top result
        let (results, _) = db.search(&query, 1, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
        assert_that!(blob_ids, elements_are![eq(&bid1)]);
        assert_that!(scores, elements_are![eq(&0.9)]);
        Ok(())
    }

    #[gtest]
    fn icing_embedding_search_expired_memory_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let past = SystemTime::now() - std::time::Duration::from_secs(3600);
        let future = SystemTime::now() + std::time::Duration::from_secs(3600);

        // Expired memory
        let mut m_expired =
            mem_with_view("expired_memory_embed", &["embed_tag"], "expired_view", &[1.0, 0.0, 0.0]);
        m_expired.expiration_timestamp = Some(system_time_to_timestamp(past));
        db.add_memory(&m_expired, "expired_blob_embed".into())?;

        // Non-expired memory (future expiration)
        let mut m_future = mem_with_view(
            "non_expired_memory_embed",
            &["embed_tag"],
            "non_expired_view",
            &[1.0, 0.0, 0.0],
        );
        m_future.expiration_timestamp = Some(system_time_to_timestamp(future));
        db.add_memory(&m_future, "non_expired_blob_embed".into())?;

        // Never-expired memory (no expiration)
        db.add_memory(
            &mem_with_view(
                "never_expired_memory_embed",
                &["embed_tag"],
                "never_expired_view",
                &[1.0, 0.0, 0.0],
            ),
            "never_expired_blob_embed".into(),
        )?;

        let query = embedding_query(&[1.0, 0.0, 0.0]);
        let (results, _) = db.search(&query, 10, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

        // Only non-expired and never-expired memories should appear.
        assert_that!(
            blob_ids,
            unordered_elements_are![eq(&"non_expired_blob_embed"), eq(&"never_expired_blob_embed")]
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

    #[gtest]
    fn icing_deduplicate_search_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let mut blob_ids_expected = vec![];
        for i in 0..5 {
            let blob_id = (1000 + i).to_string();
            let views: Vec<LlmView> = (0..2)
                .map(|j| {
                    let score = 1.0 - (i as f32 * 0.2 + j as f32 * 0.1);
                    llm_view(&format!("view_{i}_{j}"), &[score, 0.0, 0.0])
                })
                .collect();
            db.add_memory(
                &mem_with_views(&format!("memory_embed_{i}"), &["embed_tag"], views),
                blob_id.clone(),
            )?;
            blob_ids_expected.push(blob_id);
        }

        let query = embedding_query(&[1.0, 0.0, 0.0]);
        let (results, _) = db.search(&query, 2, PageToken::Start)?;
        assert_that!(results.items, len(eq(2)));

        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
        let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();

        // Memory 0: views score 1.0+0.9=1.9. Memory 1: first matching view 0.8.
        assert_that!(blob_ids, elements_are![eq(&blob_ids_expected[0]), eq(&blob_ids_expected[1])]);
        assert_that!(scores, elements_are![eq(&1.9), eq(&0.8)]);

        Ok(())
    }

    #[gtest]
    fn icing_delete_memory_also_deletes_views_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let mid = "memory_id".to_string();
        let views = vec![llm_view("view1", &[1.0, 0.0, 0.0]), llm_view("view2", &[0.0, 1.0, 0.0])];
        db.add_memory(&mem_with_views(&mid, &["tag"], views), 12345.to_string())?;

        assert_that!(
            db.get_view_ids_by_memory_id(mid.clone()),
            ok(unordered_elements_are![eq(&"view1"), eq(&"view2")])
        );
        db.delete_memories(&[mid.clone()])?;
        assert_that!(db.get_view_ids_by_memory_id(mid), ok(is_empty()));
        Ok(())
    }

    #[gtest]
    fn icing_update_memory_replaces_views_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let mid = "memory_id_to_update".to_string();

        // Add memory with two views.
        let views1 = vec![llm_view("view1", &[1.0, 0.0, 0.0]), llm_view("view2", &[0.0, 1.0, 0.0])];
        db.add_memory(&mem_with_views(&mid, &["tag"], views1), "blob_id_1".into())?;
        assert_that!(
            db.get_view_ids_by_memory_id(mid.clone())?,
            unordered_elements_are![eq(&"view1"), eq(&"view2")]
        );

        // Update: replace views with a single new view.
        db.add_memory(
            &mem_with_view(&mid, &["tag"], "view3", &[0.0, 0.0, 1.0]),
            "blob_id_2".into(),
        )?;
        assert_that!(
            db.get_view_ids_by_memory_id(mid.clone())?,
            unordered_elements_are![eq(&"view3")]
        );

        // Update again: no views.
        db.add_memory(
            &Memory { id: mid.clone(), tags: vec!["tag".into()], ..Default::default() },
            "blob_id_3".into(),
        )?;
        assert_that!(db.get_view_ids_by_memory_id(mid)?, is_empty());

        Ok(())
    }

    #[gtest]
    fn icing_search_with_view_scores_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let blob_id = "blob_id_view_scores".to_string();
        let views = vec![llm_view("view1", &[1.0, 0.0, 0.0]), llm_view("view2", &[0.0, 1.0, 0.0])];
        db.add_memory(&mem_with_views("memory_id_view_scores", &["tag"], views), blob_id.clone())?;

        let query = embedding_query(&[0.7, 0.3, 0.0]);
        let (results, _) = db.search(&query, 10, PageToken::Start)?;

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
        let mut db = IcingMetaDatabase::new(tempdir())?;

        let memory_id = "expired_memory_id".to_string();
        let blob_id = "expired_blob_id".to_string();
        let past_time = SystemTime::now() - std::time::Duration::from_secs(3600);

        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["expired".into()],
            expiration_timestamp: Some(system_time_to_timestamp(past_time)),
            ..Default::default()
        };
        db.add_memory(&memory, blob_id.clone())?;

        // Verify the memory is stored (bypassing expiration filter).
        let search_spec = icing::SearchSpecProto {
            query: Some(memory_id.to_string()),
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            type_property_filters: vec![IcingMetaDatabase::create_search_filter(
                SCHEMA_NAME,
                MEMORY_ID_NAME,
            )],
            ..Default::default()
        };
        let result_spec = icing::ResultSpecProto {
            num_per_page: Some(1),
            type_property_masks: vec![IcingMetaDatabase::create_blob_id_projection(SCHEMA_NAME)],
            ..Default::default()
        };
        let raw_result = db.icing_search_engine.search(
            &search_spec,
            &icing::get_default_scoring_spec(),
            &result_spec,
        );
        assert_that!(raw_result.as_ref().unwrap().results, len(eq(1)));
        assert_that!(
            IcingMetaDatabase::extract_blob_id_from_doc(&raw_result.unwrap().results[0]),
            eq(&Some(blob_id.clone()))
        );

        // Public API should NOT find it (expired).
        expect_that!(db.get_blob_id_by_memory_id(memory_id)?, eq(&None));

        Ok(())
    }

    #[gtest]
    fn icing_get_memory_by_name_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        db.add_memory(
            &Memory { id: "memory_id".into(), name: "memory_name".into(), ..Default::default() },
            "blob_id".into(),
        )?;

        expect_that!(db.get_memory_by_name("memory_name")?, eq(&Some("blob_id".to_string())));
        expect_that!(db.get_memory_by_name("memory_name_wrong")?, eq(&None));
        Ok(())
    }

    #[gtest]
    fn icing_get_memory_by_name_duplicate_error_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        db.add_memory(
            &Memory { id: "memory_id1".into(), name: "memory_name".into(), ..Default::default() },
            "blob_id".into(),
        )?;
        db.add_memory(
            &Memory { id: "memory_id2".into(), name: "memory_name".into(), ..Default::default() },
            "blob_id".into(),
        )?;

        expect_that!(db.get_memory_by_name("memory_name"), err(anything()));
        Ok(())
    }

    #[gtest]
    fn icing_get_memories_by_tag_with_expiration_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let past = SystemTime::now() - std::time::Duration::from_secs(3600);
        let future = SystemTime::now() + std::time::Duration::from_secs(3600);

        // Expired
        let mut m_expired = Memory {
            id: "memory_expired".into(),
            tags: vec!["test_tag".into()],
            ..Default::default()
        };
        m_expired.expiration_timestamp = Some(system_time_to_timestamp(past));
        db.add_memory(&m_expired, "blob_expired".into())?;

        // Future expiration
        let mut m_future = Memory {
            id: "memory_future".into(),
            tags: vec!["test_tag".into()],
            ..Default::default()
        };
        m_future.expiration_timestamp = Some(system_time_to_timestamp(future));
        db.add_memory(&m_future, "blob_future".into())?;

        // No expiration
        db.add_memory(
            &Memory {
                id: "memory_no_expiry".into(),
                tags: vec!["test_tag".into()],
                ..Default::default()
            },
            "blob_no_expiry".into(),
        )?;

        let (results, _) = db.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        assert_that!(results, unordered_elements_are![eq(&"blob_future"), eq(&"blob_no_expiry")]);
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

    /// Verifies delete_memories uses MemoryId (not BlobId) for deletion.
    #[gtest]
    fn delete_memories_uses_correct_id_types_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let mid = "test_memory_id".to_string();
        let bid = "test_blob_id_12345".to_string();
        db.add_memory(
            &Memory { id: mid.clone(), tags: vec!["test_tag".into()], ..Default::default() },
            bid.clone(),
        )?;

        expect_that!(db.get_blob_id_by_memory_id(mid.clone())?, eq(&Some(bid.clone())));
        let (results, _) = db.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, contains(eq(&bid)));

        db.delete_memories(&[mid.clone()])?;

        expect_that!(db.get_blob_id_by_memory_id(mid)?, eq(&None));
        let (results, _) = db.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, is_empty());

        Ok(())
    }

    /// text_search returns results sorted by created_timestamp descending.
    #[gtest]
    fn text_search_sorts_by_created_timestamp_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        // Insert in non-sorted order: old, new, mid.
        for (id, blob, secs) in [
            ("memory_old", "blob_old", 1000),
            ("memory_new", "blob_new", 3000),
            ("memory_mid", "blob_mid", 2000),
        ] {
            let m = Memory {
                id: id.into(),
                tags: vec!["sort_test".into()],
                created_timestamp: Some(ts(secs)),
                ..Default::default()
            };
            db.add_memory(&m, blob.into())?;
        }

        let text_query = TextQuery {
            field: MemoryField::Tags as i32,
            match_type: MatchType::Equal as i32,
            value: Some(text_query::Value::StringVal("sort_test".into())),
        };
        let (results, _) = db.text_search(&text_query, 10, PageToken::Start)?;
        let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

        expect_that!(blob_ids.len(), eq(3));
        expect_that!(blob_ids, elements_are![eq("blob_new"), eq("blob_mid"), eq("blob_old")]);
        Ok(())
    }

    #[gtest]
    fn get_memories_by_tag_sorts_by_created_timestamp_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        for (id, blob, secs) in [
            ("memory_old", "blob_old", 1000),
            ("memory_new", "blob_new", 3000),
            ("memory_mid", "blob_mid", 2000),
        ] {
            let m = Memory {
                id: id.into(),
                tags: vec!["sort_tag".into()],
                created_timestamp: Some(ts(secs)),
                ..Default::default()
            };
            db.add_memory(&m, blob.into())?;
        }

        let (blob_ids, _) = db.get_memories_by_tag("sort_tag", 10, PageToken::Start)?;
        expect_that!(blob_ids, elements_are![eq("blob_new"), eq("blob_mid"), eq("blob_old")]);
        Ok(())
    }

    #[gtest]
    fn get_memories_by_empty_tag_returns_all_memories_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        db.add_memory(
            &Memory { id: "memory1".into(), tags: vec!["tag_a".into()], ..Default::default() },
            "blob1".into(),
        )?;
        db.add_memory(
            &Memory { id: "memory2".into(), tags: vec!["tag_b".into()], ..Default::default() },
            "blob2".into(),
        )?;

        let (results, _) = db.get_memories_by_tag("", 10, PageToken::Start)?;
        assert_that!(results, unordered_elements_are![eq("blob1"), eq("blob2")]);
        Ok(())
    }

    // =========================================================================
    // GetDatabaseMetrics / get_document_counts tests
    // =========================================================================

    #[gtest]
    fn get_document_counts_empty_db_test() -> anyhow::Result<()> {
        let db = IcingMetaDatabase::new(tempdir())?;
        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(0));
        expect_that!(llm_view_count, eq(0));
        Ok(())
    }

    #[gtest]
    fn get_document_counts_memories_only_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        add_test_memory(&mut db, "1");
        add_test_memory(&mut db, "2");
        add_test_memory(&mut db, "3");

        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(3));
        expect_that!(llm_view_count, eq(0));
        Ok(())
    }

    #[gtest]
    fn get_document_counts_with_views_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        // Memory with 2 views.
        let views = vec![llm_view("view1", &[1.0, 0.0, 0.0]), llm_view("view2", &[0.0, 1.0, 0.0])];
        db.add_memory(&mem_with_views("mem1", &["tag"], views), "blob1".into())?;

        // Memory with 1 view.
        db.add_memory(&mem_with_view("mem2", &["tag"], "view3", &[0.0, 0.0, 1.0]), "blob2".into())?;

        // Memory with no views.
        add_test_memory(&mut db, "3");

        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(3));
        expect_that!(llm_view_count, eq(3));
        Ok(())
    }

    #[gtest]
    fn get_document_counts_after_delete_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;

        db.add_memory(&mem_with_view("mem1", &["tag"], "view1", &[1.0, 0.0, 0.0]), "blob1".into())?;
        db.add_memory(&mem_with_view("mem2", &["tag"], "view2", &[0.0, 1.0, 0.0]), "blob2".into())?;

        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(2));
        expect_that!(llm_view_count, eq(2));

        // Delete one memory (and its view).
        db.delete_memories(&["mem1".to_string()])?;

        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(1));
        expect_that!(llm_view_count, eq(1));
        Ok(())
    }

    #[gtest]
    fn get_document_counts_after_reset_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        add_test_memory(&mut db, "1");
        add_test_memory(&mut db, "2");

        let (memory_count, _) = db.get_document_counts()?;
        expect_that!(memory_count, eq(2));

        db.reset()?;

        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(0));
        expect_that!(llm_view_count, eq(0));
        Ok(())
    }

    // =========================================================================
    // Storage size tests (exported encoded_len)
    // =========================================================================

    #[gtest]
    fn export_size_grows_with_data_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let empty_size = db.export()?.encoded_len();
        assert_that!(empty_size, gt(0));

        // Add a memory without views.
        add_test_memory(&mut db, "1");
        let size_after_one = db.export()?.encoded_len();
        assert_that!(size_after_one, gt(empty_size));

        // Add a memory with views — should grow further.
        db.add_memory(&mem_with_view("mem_v", &["tag"], "v1", &[1.0, 0.0, 0.0]), "blob_v".into())?;
        let size_after_two = db.export()?.encoded_len();
        assert_that!(size_after_two, gt(size_after_one));

        Ok(())
    }

    #[gtest]
    fn export_size_shrinks_after_reset_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(tempdir())?;
        let empty_size = db.export()?.encoded_len();

        add_test_memory(&mut db, "1");
        add_test_memory(&mut db, "2");
        db.add_memory(&mem_with_view("mem_v", &["tag"], "v1", &[1.0, 0.0, 0.0]), "blob_v".into())?;
        let size_with_data = db.export()?.encoded_len();
        assert_that!(size_with_data, gt(empty_size));

        db.reset()?;
        let size_after_reset = db.export()?.encoded_len();
        // After reset the DB should be back to roughly its empty size.
        assert_that!(size_after_reset, lt(size_with_data));

        Ok(())
    }
}
