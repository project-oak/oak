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
use std::time::SystemTime;

use anyhow::{Context, bail, ensure};
use external_db_client::BlobId;
use icing::{DocumentProto, IcingGroundTruthFilesHelper};
use log::{debug, error, info};
use prost::Message;
use rand::Rng;
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, search_memories_filter},
    prelude::v1::*,
};

use crate::{MemoryId, ViewId, clock::system_time_to_timestamp};

/// Configuration for the icing search engine database.
///
/// This struct bundles all icing-level tuning knobs so that adding future
/// options does not require threading additional parameters through the
/// entire call chain.
#[derive(Debug)]
pub struct IcingDatabaseConfig {
    /// The temporary directory for the icing database files.
    pub base_dir: IcingTempDir,
    /// When true, the embedding index uses 8-bit quantization
    /// (`QUANTIZE_8_BIT`), reducing index size with negligible recall loss.
    /// Icing quantizes float embeddings internally; callers still send
    /// float values.
    pub enable_int8_embedding: bool,
}

fn timestamp_to_i64(timestamp: &prost_types::Timestamp) -> i64 {
    timestamp.seconds.saturating_mul(1_000_000_000).saturating_add(timestamp.nanos as i64)
}

// A simple struct to manage the temporary location of the icing database.
//
// The directory will be deleted when the struct is dropped, if possible. If
// deletion fails, an info message will be logged.
#[derive(Debug)]
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
    // Note: icing_search_engine must come before config.base_dir, so that it is
    // dropped before the temp dir is dropped and deleted.
    icing_search_engine: cxx::UniquePtr<icing::IcingSearchEngine>,
    applied_operations: Vec<MutationOperation>,
    config: IcingDatabaseConfig,
}

// Safety: `IcingMetaDatabase` wraps `cxx::UniquePtr<IcingSearchEngine>` which
// is `!Send` and `!Sync` by default. We manually implement both because:
//
// - **Send**: The `UniquePtr` provides exclusive ownership, so it is safe to
//   move to another thread.
// - **Sync**: The C++ `IcingSearchEngine` uses an internal `shared_mutex`
//   (`absl_ports::shared_mutex`) that protects all public methods. Read
//   operations (Search, Get, etc.) acquire a shared lock, and write operations
//   (Put, Delete, etc.) acquire an exclusive lock. This makes concurrent
//   `&IcingSearchEngine` access from multiple threads safe.
//
// See: icing-search-engine.h — all public methods are annotated with
// `ICING_LOCKS_EXCLUDED(mutex_)`, and the mutex is declared as:
//   `absl_ports::shared_mutex mutex_;`  (line 704)
// Source: <https://android.googlesource.com/platform/external/icing/+/refs/heads/main/icing/icing-search-engine.h>
unsafe impl Send for IcingMetaDatabase {}
unsafe impl Sync for IcingMetaDatabase {}

const NAMESPACE_NAME: &str = "namespace";
const SCHEMA_NAME: &str = "Memory";
const TAG_NAME: &str = "tag";
const NAME_NAME: &str = "name";
const MEMORY_ID_NAME: &str = "memoryId";
const MEMORY_QUALIFIED_ID_NAME: &str = "memoryQualifiedId";
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

    // A memory was added (or upserted). The content blob will have been written
    // separately; this operation contains the metadata and associated views that
    // need to be re-written to a new database version on version conflicts.
    AddMemory { metadata: PendingMetadata, views: Vec<PendingLlmViewMetadata> },

    // The item with the given ID was removed. The associated blob ID is
    // recorded so that the external blob soft-delete can be deferred until
    // after the Icing index has been successfully persisted (crash consistency).
    // Note that exact operation timing is not maintained. So if another session
    // wrote this ID later than the remove occurred, but wrote its metadatabase
    // back earlier, this remove would still result in removing the item.
    Remove { memory_id: MemoryId, blob_id: BlobId },

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
            let timestamp_ms = created_timestamp
                .seconds
                .saturating_mul(1000)
                .saturating_add(i64::from(created_timestamp.nanos) / 1_000_000);
            let timestamp_ms = std::cmp::max(0, timestamp_ms) as u64;
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

    /// Extracts the memory ID from the document's string properties.
    pub fn memory_id(&self) -> Option<&str> {
        self.get_string_property(MEMORY_ID_NAME)
    }

    /// Extracts the memory name from the document's string properties.
    /// Returns `None` if unnamed.
    pub fn name(&self) -> Option<&str> {
        self.get_string_property(NAME_NAME)
    }

    fn get_string_property(&self, property_name: &str) -> Option<&str> {
        self.icing_document
            .properties
            .iter()
            .find(|prop| prop.name.as_deref() == Some(property_name))?
            .string_values
            .first()
            .map(|s| s.as_str())
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
    pub fn new(
        memory: &Memory,
        view: &LlmView,
        blob_id: &BlobId,
        enable_int8_embedding: bool,
    ) -> anyhow::Result<Option<Self>> {
        let memory_id = &memory.id;
        let view_id = &view.id;
        let view_type: &String = &view.r#type;
        let name = &memory.name;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let qualified_memory_id = format!("{NAMESPACE_NAME}#{memory_id}");

        let embedding = if let Some(e) = view.embedding.as_ref() {
            e
        } else {
            return Ok(None);
        };
        let embeddings = vec![if enable_int8_embedding {
            icing::create_quantized_vector_proto(
                embedding.model_signature.as_str(),
                &embedding.values,
            )
        } else {
            icing::create_vector_proto(embedding.model_signature.as_str(), &embedding.values)
        }];
        let document_builder = icing::create_document_builder();
        let document_builder = document_builder
            .set_key(NAMESPACE_NAME.as_bytes(), view_id.as_bytes())
            .set_schema(LLM_VIEW_SCHEMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(
                MEMORY_QUALIFIED_ID_NAME.as_bytes(),
                &[qualified_memory_id.as_bytes()],
            )
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
                crate::icing::PendingLlmViewMetadata::new(memory, view, &dummy_blob_id, false)?
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

    fn create_memory_and_blob_id_projection(schema_name: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(schema_name.to_string()),
            paths: vec![MEMORY_ID_NAME.to_string(), BLOB_ID_NAME.to_string()],
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

    fn create_schema(config: &IcingDatabaseConfig) -> anyhow::Result<icing::SchemaProto> {
        let schema_type_builder = icing::create_schema_type_config_builder();
        schema_type_builder
            .set_type(SCHEMA_NAME.as_bytes())
            .add_property(
                icing::create_property_config_builder()
                    .set_name(TAG_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Verbatim.into(),
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
                        icing::string_indexing_config::tokenizer_type::Code::Verbatim.into(),
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
                    .set_name(MEMORY_QUALIFIED_ID_NAME.as_bytes())
                    .set_data_type_joinable_string(
                        icing::joinable_config::value_type::Code::QualifiedId.into(),
                    )
                    .set_cardinality(
                        icing::property_config_proto::cardinality::Code::Optional.into(),
                    ),
            )
            .add_property(
                icing::create_property_config_builder()
                    .set_name(TAG_NAME.as_bytes())
                    .set_data_type_string(
                        icing::term_match_type::Code::ExactOnly.into(),
                        icing::string_indexing_config::tokenizer_type::Code::Verbatim.into(),
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
                        icing::string_indexing_config::tokenizer_type::Code::Verbatim.into(),
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
            );

        // Build the embedding property separately so the UniquePtr lives long
        // enough for the `add_property` borrow.
        let embedding_property = icing::create_property_config_builder();
        embedding_property.set_name(EMBEDDING_NAME.as_bytes());
        let quantization_type = if config.enable_int8_embedding {
            icing::embedding_indexing_config::quantization_type::Code::Quantize8Bit
        } else {
            icing::embedding_indexing_config::quantization_type::Code::None
        };
        embedding_property.set_data_type_vector_quantized(
            icing::embedding_indexing_config::embedding_indexing_type::Code::LinearSearch.into(),
            quantization_type.into(),
        );
        embedding_property
            .set_cardinality(icing::property_config_proto::cardinality::Code::Optional.into());
        memory_view_schema_type_builder
            .add_property(&embedding_property)
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

        let schema_builder = icing::create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        schema_builder.add_type(&memory_view_schema_type_builder);
        schema_builder.build()
    }

    /// Create a new icing database. If there is already a icing
    /// db in `config.base_dir`, the old one will be deleted.
    pub fn new(config: IcingDatabaseConfig) -> anyhow::Result<Self> {
        debug!("Creating new icing database in {}", config.base_dir.as_str());
        let icing_search_engine = Self::initialize_icing_database(config.base_dir.as_str())?;
        let schema = Self::create_schema(&config)?;
        let result_proto = icing_search_engine.set_schema(&schema)?;
        ensure!(
            result_proto.status.context("set_schema returned no status in new")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        Ok(Self {
            icing_search_engine,
            applied_operations: vec![MutationOperation::Create],
            config,
        })
    }

    /// Create a new icing database using the provided import data.
    pub fn import(data: impl bytes::Buf, config: IcingDatabaseConfig) -> anyhow::Result<Self> {
        debug!("Importing icing database into {}", config.base_dir.as_str());
        let ground_truth = icing::IcingGroundTruthFiles::decode(data)?;
        ground_truth.migrate(config.base_dir.as_str())?;

        let icing_search_engine = Self::initialize_icing_database(config.base_dir.as_str())?;
        // Ensure schema is up-to-date after import (handles schema migrations).
        let schema = Self::create_schema(&config)?;
        let result_proto = icing_search_engine.set_schema(&schema)?;
        ensure!(
            result_proto.status.context("set_schema in import failed")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        Ok(Self { icing_search_engine, applied_operations: vec![], config })
    }

    fn initialize_icing_database(
        base_dir_str: &str,
    ) -> anyhow::Result<cxx::UniquePtr<icing::IcingSearchEngine>> {
        let options_bytes = icing::get_default_icing_options(base_dir_str).encode_to_vec();
        let icing_search_engine = icing::create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize()?;
        ensure!(
            result_proto.status.context("initialize returned no status")?.code
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
        let mut pending_views: Vec<PendingLlmViewMetadata> = Vec::new();
        if let Some(views) = memory.views.as_ref() {
            for view in &views.llm_views {
                // TODO: yongheng - Generate view id if not provided.
                if let Some(pending_view_metadata) = PendingLlmViewMetadata::new(
                    memory,
                    view,
                    &blob_id,
                    self.config.enable_int8_embedding,
                )? {
                    pending_views.push(pending_view_metadata);
                }
            }
        }
        self.put_memory_with_views(pending_metadata, pending_views)
    }

    /// Puts the memory metadata and its associated views into the Icing index
    /// and records a single `AddMemory` operation in the mutation log.
    fn put_memory_with_views(
        &mut self,
        metadata: PendingMetadata,
        views: Vec<PendingLlmViewMetadata>,
    ) -> anyhow::Result<()> {
        let result = self.icing_search_engine.put(metadata.document())?;
        ensure!(
            result.status.context("put memory returned no status at put_memory_with_views")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        for view in &views {
            let result = self.icing_search_engine.put(view.document())?;
            if result.status.clone().context("put view returned no status")?.code
                != Some(icing::status_proto::Code::Ok.into())
            {
                debug!("{:?}", result);
            }
            ensure!(
                result.status.context("put view returned no status (ensure)")?.code
                    == Some(icing::status_proto::Code::Ok.into())
            );
        }
        self.applied_operations.push(MutationOperation::AddMemory { metadata, views });
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
        let scoring_spec = icing::ScoringSpecProto {
            rank_by: Some(
                icing::scoring_spec_proto::ranking_strategy::Code::CreationTimestamp.into(),
            ),
            ..Default::default()
        };
        let projection = Self::create_blob_id_projection(SCHEMA_NAME);
        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &scoring_spec,
            page_size,
            None,
            page_token,
            projection,
        )?;
        let blob_ids = Self::extract_blob_ids_from_search_result(search_result);
        if blob_ids.is_empty() {
            return Ok((blob_ids, PageToken::Start));
        }
        Ok((blob_ids, next_page_token))
    }

    pub fn get_memory_metadata_by_name(
        &self,
        name: &str,
    ) -> anyhow::Result<Option<(MemoryId, BlobId)>> {
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
            num_per_page: Some(2),
            type_property_masks: vec![Self::create_memory_and_blob_id_projection(SCHEMA_NAME)],
            ..Default::default()
        };

        let search_result: icing::SearchResultProto = self.icing_search_engine.search(
            &search_spec,
            &icing::get_default_scoring_spec(),
            &result_spec,
        )?;

        if search_result
            .status
            .clone()
            .context("get_memory_metadata_by_name search returned no status")?
            .code
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

        Ok(search_result.results.first().and_then(Self::extract_metadata_from_doc))
    }

    pub fn get_memory_by_name(&self, name: &str) -> anyhow::Result<Option<BlobId>> {
        Ok(self.get_memory_metadata_by_name(name)?.map(|(_, bid)| bid))
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

        if search_result
            .status
            .clone()
            .context("get_blob_id_by_memory_id search returned no status")?
            .code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for memory_id {}: {:?}", memory_id, search_result.status);
        }

        // Extract the blob_id from the first result, if any.
        match search_result.results.first() {
            None => Ok(None),
            Some(doc) => {
                let blob_id = Self::extract_blob_id_from_doc(doc)
                    .context("memory document exists but has no blob_id property")?;
                Ok(Some(blob_id))
            }
        }
    }

    fn extract_view_ids_from_search_result(search_result: icing::SearchResultProto) -> Vec<ViewId> {
        search_result.results.iter().filter_map(Self::extract_view_id_from_doc).collect::<Vec<_>>()
    }

    pub fn optimize(&self) -> anyhow::Result<icing::OptimizeResultProto> {
        self.icing_search_engine.optimize()
    }

    pub fn get_optimize_info(&self) -> anyhow::Result<icing::GetOptimizeInfoResultProto> {
        self.icing_search_engine.get_optimize_info()
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
        if search_result
            .status
            .clone()
            .context("get_view_ids_by_memory_id search returned no status")?
            .code
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

    fn extract_metadata_from_doc(
        doc_hit: &icing::search_result_proto::ResultProto,
    ) -> Option<(MemoryId, BlobId)> {
        let doc = doc_hit.document.as_ref()?;
        let mut memory_id = None;
        let mut blob_id = None;

        let memory_id_name = MEMORY_ID_NAME.to_string();
        let blob_id_name = BLOB_ID_NAME.to_string();

        for prop in &doc.properties {
            if prop.name.as_ref() == Some(&memory_id_name) {
                memory_id = prop.string_values.first().cloned();
            } else if prop.name.as_ref() == Some(&blob_id_name) {
                blob_id = prop.string_values.first().cloned();
            }
        }

        match (memory_id, blob_id) {
            (Some(mid), Some(bid)) => Some((mid, bid)),
            _ => None,
        }
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
                query: Some(format!("hasProperty(\"{}\")", BLOB_ID_NAME)),
                enabled_features: vec![
                    icing::HAS_PROPERTY_FUNCTION_FEATURE.to_string(),
                    icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
                ],
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

            if search_result
                .status
                .clone()
                .context("get_all_memory_ids search returned no status")?
                .code
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
        let now_ts = timestamp_to_i64(&system_time_to_timestamp(SystemTime::now()));
        let search_spec = icing::SearchSpecProto {
            query: Some(format!("({} < {})", EXPIRATION_TIMESTAMP_NAME, now_ts)),
            enabled_features: vec!["NUMERIC_SEARCH".to_string()],
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            ..Default::default()
        };
        let projection = Self::create_memory_id_projection(SCHEMA_NAME);
        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &icing::ScoringSpecProto::default(),
            page_size,
            None,
            page_token,
            projection,
        )?;
        let ids = Self::extract_memory_ids_from_search_result(search_result.clone());
        if ids.is_empty() { Ok((ids, PageToken::Start)) } else { Ok((ids, next_page_token)) }
    }

    pub fn reset(&mut self) -> anyhow::Result<()> {
        let result_bytes = self.icing_search_engine.reset();
        let result = icing::ResetResultProto::decode(result_bytes.as_slice())?;
        ensure!(
            result.status.clone().context("reset returned no status")?.code
                == Some(icing::status_proto::Code::Ok.into()),
            "Icing reset failed: {:?}",
            result.status
        );

        let schema = Self::create_schema(&self.config)?;
        let set_schema_result = self.icing_search_engine.set_schema(&schema)?;
        ensure!(
            set_schema_result.status.clone().context("set_schema returned no status")?.code
                == Some(icing::status_proto::Code::Ok.into()),
            "Icing set_schema failed: {:?}",
            set_schema_result.status
        );

        self.applied_operations.push(MutationOperation::Reset);
        Ok(())
    }

    fn execute_search(
        &self,
        search_spec: &icing::SearchSpecProto,
        scoring_spec: &icing::ScoringSpecProto,
        page_size: i32,
        limit: Option<i32>,
        page_token: PageToken,
        result_projection: icing::TypePropertyMask,
    ) -> anyhow::Result<(icing::SearchResultProto, PageToken)> {
        const DEFAULT_PAGE_SIZE: i32 = 10;
        let num_per_page = if page_size > 0 { page_size } else { DEFAULT_PAGE_SIZE };

        let mut result_spec = icing::ResultSpecProto {
            num_per_page: Some(num_per_page),
            num_to_score: Some(i32::MAX),
            ..Default::default()
        };

        if let Some(limit_val) = limit {
            result_spec.result_group_type =
                Some(icing::result_spec_proto::ResultGroupingType::Namespace as i32);
            result_spec.result_groupings = vec![icing::result_spec_proto::ResultGrouping {
                entry_groupings: vec![icing::result_spec_proto::result_grouping::Entry {
                    namespace: Some(NAMESPACE_NAME.to_string()),
                    schema: None,
                }],
                max_results: Some(limit_val),
            }];
        }

        result_spec.type_property_masks.push(result_projection);

        let search_result = match page_token {
            PageToken::Start => {
                self.icing_search_engine.search(search_spec, scoring_spec, &result_spec)?
            }
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token)?,
            PageToken::Invalid => bail!("invalid page token"),
        };

        if search_result.status.clone().context("execute_search returned no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for {:?}", search_result.status);
        }

        let next_page_token =
            search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
        Ok((search_result, next_page_token))
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
        // Build the Icing search spec from the filter tree.
        let mut search_spec = self.build_search_memories_filter(&request.filter)?;

        let scoring_spec = Self::build_search_memories_sort(&request.sort, &mut search_spec)?;

        debug!("search_spec: {:?}", search_spec);
        debug!("scoring_spec: {:?}", scoring_spec);

        let page_size = request.page_size;

        let page_token = PageToken::try_from(request.page_token.clone())
            .map_err(|e| anyhow::anyhow!("invalid page token: {}", e))?;

        let projection = icing::TypePropertyMask {
            schema_type: Some(SCHEMA_NAME.to_string()),
            paths: vec![BLOB_ID_NAME.to_string()],
        };

        let limit = if request.limit > 0 { Some(request.limit) } else { None };

        let (search_result, next_page_token) = self.execute_search(
            &search_spec,
            &scoring_spec,
            page_size,
            limit,
            page_token,
            projection,
        )?;

        debug!("search_result: {:?}", search_result);

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
    fn build_search_memories_sort(
        sorts: &[SearchMemoriesSort],
        search_spec: &mut icing::SearchSpecProto,
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
            Sort::EmbeddingSort(emb) => Self::build_embedding_sort(emb, search_spec),
        }
    }

    fn build_embedding_sort(
        sort: &EmbeddingSort,
        search_spec: &mut icing::SearchSpecProto,
    ) -> anyhow::Result<icing::ScoringSpecProto> {
        if let Some(query) = &search_spec.query
            && query.contains("getEmbeddingParameter")
        {
            bail!("Sorting and filtering by embedding at the same time currently not implemented");
        }

        let embedding = sort.embedding.as_ref().context("EmbeddingSort.embedding is required")?;

        if sort.order() == SortOrder::OrderAscending {
            bail!("Ascending embedding order currently not implemented");
        }

        let mut query_string = "semanticSearch(getEmbeddingParameter(0))".to_string();
        if !sort.view_type.is_empty() {
            query_string = format!("({}:{}) AND {}", VIEW_TYPE_NAME, sort.view_type, query_string);
        }

        search_spec.join_spec = Some(Box::new(icing::JoinSpecProto {
            parent_property_expression: Some("this.qualifiedId()".to_string()),
            child_property_expression: Some(MEMORY_QUALIFIED_ID_NAME.to_string()),
            nested_spec: Some(Box::new(icing::join_spec_proto::NestedSpecProto {
                search_spec: Some(Box::new(icing::SearchSpecProto {
                    query: Some(query_string),
                    term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
                    schema_type_filters: vec![LLM_VIEW_SCHEMA_NAME.to_string()],
                    embedding_query_metric_type: Some(
                        icing::search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
                    ),
                    embedding_query_vectors: vec![icing::create_vector_proto(
                        embedding.model_signature.as_str(),
                        &embedding.values,
                    )],
                    enabled_features: vec![icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()],
                    ..Default::default()
                })),
                scoring_spec: Some(icing::ScoringSpecProto {
                    rank_by: Some(
                        icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
                    ),
                    advanced_scoring_expression: Some(
                        "sum(this.matchedSemanticScores(getEmbeddingParameter(0)))".to_string(),
                    ),
                    ..Default::default()
                }),
                ..Default::default()
            })),
            ..Default::default()
        }));

        let scoring_spec = icing::ScoringSpecProto {
            rank_by: Some(
                icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
            ),
            // We take the max of embedding scores and (creation time - 1e20).
            // Since embedding scores are in the range 0-1, this ensures any memory
            // with embeddings will be ranked above any memory without.
            advanced_scoring_expression: Some(
                "maxOrDefault(this.childrenRankingSignals(), this.creationTimestamp() - 1e20)"
                    .to_string(),
            ),
            order_by: Some(icing::scoring_spec_proto::order::Code::Desc.into()),
            ..Default::default()
        };

        Ok(scoring_spec)
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
        filter: &Option<SearchMemoriesFilter>,
    ) -> anyhow::Result<icing::SearchSpecProto> {
        use search_memories_filter::Value;
        let value = match filter.as_ref().and_then(|f| f.value.as_ref()) {
            // No filter provided, default to selecting everything.
            Some(v) => v,
            None => {
                return Ok(icing::SearchSpecProto {
                    schema_type_filters: vec![SCHEMA_NAME.to_string()],
                    ..Default::default()
                });
            }
        };
        match value {
            Value::IdFilter(f) => self.build_string_filter_spec(MEMORY_ID_NAME, &f.value),
            Value::NameFilter(f) => self.build_string_filter_spec(NAME_NAME, &f.value),
            Value::TagsFilter(f) => self.build_string_filter_spec(TAG_NAME, &f.value),
            Value::CreatedTimestampFilter(f) => {
                self.build_time_filter_spec(CREATED_TIMESTAMP_NAME, f)
            }
            Value::EventTimestampFilter(f) => self.build_time_filter_spec(EVENT_TIMESTAMP_NAME, f),
            Value::ExpirationTimestampFilter(f) => {
                self.build_time_filter_spec(EXPIRATION_TIMESTAMP_NAME, f)
            }
            Value::EmbeddingFilter(f) => self.build_embedding_filter_spec(f),
            Value::AndOperator(filters) => self.build_composite_filter(&filters.filters, "AND"),
            Value::OrOperator(filters) => self.build_composite_filter(&filters.filters, "OR"),
            Value::NotOperator(inner) => {
                let mut child = self.build_search_memories_filter(&Some((**inner).clone()))?;
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
    ) -> anyhow::Result<icing::SearchSpecProto> {
        ensure!(!filters.is_empty(), "composite filter must have at least one child");
        let mut sub_queries = Vec::new();
        let mut embedding_filter_count = 0;
        let mut merged_features: Vec<String> = Vec::new();
        let mut merged_spec = icing::SearchSpecProto::default();

        for child_filter in filters {
            let child = self.build_search_memories_filter(&Some(child_filter.clone()))?;
            if let Some(q) = child.query {
                if q.contains("getEmbeddingParameter") {
                    embedding_filter_count += 1;
                    ensure!(
                        embedding_filter_count <= 1,
                        "Multiple embedding filters not currently implemented"
                    );
                }
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
            if child.embedding_query_metric_type.is_some() {
                merged_spec.embedding_query_metric_type = child.embedding_query_metric_type;
            }
            if !child.embedding_query_vectors.is_empty() {
                merged_spec.embedding_query_vectors.extend(child.embedding_query_vectors);
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
    ) -> anyhow::Result<icing::SearchSpecProto> {
        let escaped_value = value.replace('"', "\\\"");
        let query_string = format!("({field_name}:\"{escaped_value}\")");
        let search_spec = icing::SearchSpecProto {
            query: Some(query_string),
            enabled_features: vec![
                "NUMERIC_SEARCH".to_string(),
                "VERBATIM_SEARCH".to_string(),
                icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
            ],
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            ..Default::default()
        };
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
        let search_spec = icing::SearchSpecProto {
            query: Some(query_string),
            enabled_features: vec![
                "NUMERIC_SEARCH".to_string(),
                icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string(),
            ],
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            schema_type_filters: vec![SCHEMA_NAME.to_string()],
            ..Default::default()
        };
        Ok(search_spec)
    }

    pub fn delete_document(&mut self, blob_id: &BlobId) -> anyhow::Result<()> {
        let result =
            self.icing_search_engine.delete(NAMESPACE_NAME.as_bytes(), blob_id.as_bytes())?;
        if result.status.clone().context("delete_document returned no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Failed to delete document with id {}: {:?}", blob_id, result.status);
        }
        Ok(())
    }

    /// Deletes the given memories from the database. Returns the IDs of any
    /// memories that were not found (these are silently skipped).
    pub fn delete_memories(&mut self, memory_ids: &[MemoryId]) -> anyhow::Result<Vec<MemoryId>> {
        let mut not_found_ids = Vec::new();
        for memory_id in memory_ids {
            // Resolve the blob ID before deleting the document, since the
            // mapping lives inside the Icing document itself.
            match self.get_blob_id_by_memory_id(memory_id.clone())? {
                Some(blob_id) => {
                    self.delete_memory_documents(memory_id)?;
                    self.applied_operations
                        .push(MutationOperation::Remove { memory_id: memory_id.clone(), blob_id });
                }
                None => {
                    not_found_ids.push(memory_id.clone());
                }
            }
        }
        Ok(not_found_ids)
    }

    /// Remove memory documents from the Icing index without recording a
    /// mutation. Used during rebase replay for AddMemory upsert cleanup
    /// where the deleted documents belong to the remote base.
    fn delete_memory_documents(&mut self, memory_id: &MemoryId) -> anyhow::Result<()> {
        let view_ids = self.get_view_ids_by_memory_id(memory_id.clone())?;
        for view_id in view_ids {
            self.delete_document(&view_id)?;
        }
        self.delete_document(memory_id)
    }

    /// Returns the blob IDs from all `Remove` operations in the mutation log.
    ///
    /// These are the blobs whose external storage should be soft-deleted
    /// after the Icing index has been successfully persisted.
    pub fn pending_blob_deletes(&self) -> Vec<BlobId> {
        self.applied_operations
            .iter()
            .filter_map(|op| match op {
                MutationOperation::Remove { blob_id, .. } => Some(blob_id.clone()),
                _ => None,
            })
            .collect()
    }

    /// Returns true if this instance was created fresh, without any previously
    /// existing data.
    pub fn needs_writeback(&self) -> bool {
        !self.applied_operations.is_empty()
    }

    /// Clear the mutation log after the database has been successfully
    /// persisted. Without this, stale operations would be replayed on
    /// subsequent rebases, causing spurious upserts and redundant persists.
    pub fn mark_persisted(&mut self) {
        self.applied_operations.clear();
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
    ) -> anyhow::Result<(Self, usize)> {
        let config = IcingDatabaseConfig {
            base_dir: new_base_dir,
            enable_int8_embedding: apply_changes_from.config.enable_int8_embedding,
        };
        let mut new_db = Self::import(new_base_blob, config)?;
        let mut failed_operations: usize = 0;

        // Apply each operation to the new database.
        // This will also recreate the applied operations on the new database as a side
        // effect, in case it also needs to be rebased.
        for operation in apply_changes_from.applied_operations.iter() {
            let result = match operation {
                MutationOperation::Create => {
                    // No action, now the database is created.
                    Ok(())
                }
                MutationOperation::AddMemory { metadata, views } => {
                    // Enforce name uniqueness: if a memory with the same name
                    // already exists in the new base, delete it first. This
                    // mirrors the handler-level semantics where a name
                    // identifies a unique memory.
                    if let Some(name) = metadata.name()
                        && let Ok(Some((existing_id, _))) = new_db.get_memory_metadata_by_name(name)
                    {
                        let _ = new_db.delete_memory_documents(&existing_id);
                    }
                    // Also handle ID-based upsert: if the memory ID already
                    // exists, delete it first to clear stale views.
                    if let Some(memory_id) = metadata.memory_id()
                        && let Ok(Some(_)) = new_db.get_blob_id_by_memory_id(memory_id.to_string())
                    {
                        let _ = new_db.delete_memory_documents(&memory_id.to_string());
                    }
                    new_db.put_memory_with_views(metadata.clone(), views.clone())
                }
                MutationOperation::Remove { memory_id, .. } => {
                    // Replay the user's delete. If the memory still exists in
                    // the new base, delete_memories records a fresh Remove
                    // with the correct blob_id. If it's already gone, it is
                    // silently skipped.
                    new_db.delete_memories(&[memory_id.to_string()]).map(|_| ())
                }
                MutationOperation::Reset => Ok(new_db.reset()?),
            };

            if result.is_err() {
                error!("Warning: failed to apply operation onto new database");
                failed_operations += 1;
            }
        }

        Ok((new_db, failed_operations))
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
                num_to_score: Some(i32::MAX),
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

            if search_result
                .status
                .clone()
                .context("count_documents_by_schema search returned no status")?
                .code
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
            result_proto.status.context("persist_to_disk returned no status in export")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        icing::IcingGroundTruthFiles::new(self.config.base_dir.as_str())
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

    fn test_config() -> IcingDatabaseConfig {
        IcingDatabaseConfig { base_dir: tempdir(), enable_int8_embedding: false }
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
        let mut db = IcingMetaDatabase::new(test_config())?;

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
        let config = test_config();
        let base_dir_string = config.base_dir.as_str().to_string();
        let mut db = IcingMetaDatabase::new(config)?;

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

        let imported_db = IcingMetaDatabase::import(exported_data.as_slice(), test_config())
            .expect("failed to import");

        expect_that!(
            imported_db.get_blob_id_by_memory_id(memory_id1)?,
            eq(&Some(blob_id1.clone()))
        );
        let (result, _) = imported_db.get_memories_by_tag("export_tag", 10, PageToken::Start)?;
        assert_that!(result, unordered_elements_are![eq(&blob_id1)]);
        Ok(())
    }

    /// Imports a golden icing export snapshot that was generated with a
    /// *previous* schema version and verifies that the current code can still
    /// read, search, and extend the data. If someone changes the schema in a
    /// way that breaks backward compatibility, this test will fail.
    ///
    /// To regenerate the golden file after an intentional schema change:
    /// ```
    /// bazel run //database/tools:generate_golden_export -- \
    ///     $(pwd)/database/testdata/golden_icing_export.pb
    /// ```
    #[gtest]
    fn import_golden_snapshot_preserves_data() -> anyhow::Result<()> {
        let r = runfiles::Runfiles::create().expect("failed to init runfiles");
        let golden_path =
            runfiles::rlocation!(r, "oak_private_memory/database/testdata/golden_icing_export.pb")
                .expect("missing golden export snapshot");
        let golden_bytes =
            std::fs::read(&golden_path).expect("failed to read golden export snapshot");

        let mut imported_db = IcingMetaDatabase::import(golden_bytes.as_slice(), test_config())?;

        // 1. Plain memory metadata is intact.
        assert_eq!(
            imported_db.get_blob_id_by_memory_id("golden_plain".into())?,
            Some("golden_blob_plain".to_string()),
        );

        // 2. Named memory is findable by name.
        assert_eq!(
            imported_db.get_memory_by_name("my_golden_memory")?,
            Some("golden_blob_named".to_string()),
        );

        // 3. Tag search works (requires metadata schema indexing).
        let (tag_results, _) =
            imported_db.get_memories_by_tag("golden_tag", 10, PageToken::Start)?;
        assert_that!(
            tag_results,
            unordered_elements_are![
                eq(&"golden_blob_plain".to_string()),
                eq(&"golden_blob_named".to_string()),
                eq(&"golden_blob_view".to_string())
            ]
        );

        // 5. Writing new memories after import succeeds (schema must be set).
        let new_mem = mem_with_view("new_mem", &["new_tag"], "v_new", &[0.0, 1.0, 0.0]);
        imported_db.add_memory(&new_mem, "new_blob".into())?;
        let (new_results, _) = imported_db.get_memories_by_tag("new_tag", 10, PageToken::Start)?;
        assert_that!(new_results, unordered_elements_are![eq(&"new_blob".to_string())]);

        Ok(())
    }

    #[gtest]
    fn icing_get_blob_id_by_memory_id_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

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
    fn get_all_memory_ids_finds_memory_without_timestamp() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

        let bid = 98765.to_string();
        // Create memory without created_timestamp
        db.add_memory(
            &Memory { id: "no_ts".into(), tags: vec!["tag".into()], ..Default::default() },
            bid.clone(),
        )?;

        let memory_ids = db.get_all_memory_ids()?;
        assert_that!(memory_ids, elements_are![eq("no_ts")]);

        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_add_memory() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (_mid_a, bid_a) = add_test_memory(&mut db1, "A");
        let (_mid_b, bid_b) = add_test_memory(&mut db1, "B");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer adds E and F
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let (_mid_c, bid_c) = add_test_memory(&mut db2, "C");
        let (_mid_d, bid_d) = add_test_memory(&mut db2, "D");

        // First concurrent changer import and first changer adds G and H
        let mut db3 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let (_mid_e, bid_e) = add_test_memory(&mut db3, "E");
        let (_mid_f, bid_f) = add_test_memory(&mut db3, "F");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let (db3_prime, _) =
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
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (_mid_a, bid_a) = add_test_memory(&mut db1, "A");
        let (mid_b, _mid_b) = add_test_memory(&mut db1, "B");
        let (mid_c, _bid_c) = add_test_memory(&mut db1, "C");
        let (_mid_d, bid_d) = add_test_memory(&mut db1, "D");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer removes B, adds E
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        db2.delete_memories(std::slice::from_ref(&mid_b))?;
        let (_mid_e, bid_e) = add_test_memory(&mut db2, "E");

        // Second concurrent changer import and first changer removes B and C, add F
        // The remove will be redundant, but should not cause error or failures.
        let mut db3 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        db3.delete_memories(&[mid_b.clone(), mid_c.clone()])?;
        let (_mid_f, bid_f) = add_test_memory(&mut db3, "F");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let (db3_prime, _) =
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
    fn icing_import_with_changes_test_add_memory_with_views() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (_mid_a, bid_a) = add_test_memory(&mut db1, "A");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer adds B
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let (_mid_b, bid_b) = add_test_memory(&mut db2, "B");
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // Second concurrent changer adds C with a view
        let mut db3 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let bid_c = 99999.to_string();
        db3.add_memory(&mem_with_view("C", &["tag"], "view_c", &[1.0, 0.0, 0.0]), bid_c.clone())?;

        // Rebase db3 on top of db2
        let (db3_prime, _) =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        // Should contain all items.
        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((
                unordered_elements_are![eq(bid_a.as_str()), eq(bid_b.as_str()), eq(bid_c.as_str()),],
                eq(&PageToken::Start),
            ))
        );

        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_name_uniqueness() -> anyhow::Result<()> {
        // Original base db.
        let db1 = IcingMetaDatabase::new(test_config())?;

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer adds memory with name "shared_name"
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let mem_a = Memory {
            id: "A".to_string(),
            tags: vec!["tag".to_string()],
            name: "shared_name".to_string(),
            ..Default::default()
        };
        let bid_a = "blob_a".to_string();
        db2.add_memory(&mem_a, bid_a.clone())?;
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // Second concurrent changer also adds memory with name "shared_name" but
        // different ID
        let mut db3 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let mem_b = Memory {
            id: "B".to_string(),
            tags: vec!["tag".to_string()],
            name: "shared_name".to_string(),
            ..Default::default()
        };
        let bid_b = "blob_b".to_string();
        db3.add_memory(&mem_b, bid_b.clone())?;

        // Rebase db3 on top of db2
        let (db3_prime, _) =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        // The memory from db3 (bid_b) should have overwritten the one from db2 (bid_a)
        // So only bid_b should be present for the tag.
        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((elements_are![eq(bid_b.as_str())], eq(&PageToken::Start),))
        );

        Ok(())
    }

    #[gtest]
    fn icing_import_with_changes_test_reset() -> anyhow::Result<()> {
        // Original base db.
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (_mid_a, _bid_a) = add_test_memory(&mut db1, "A");
        let (mid_b, _bid_b) = add_test_memory(&mut db1, "B");
        let (_mid_c, _bid_c) = add_test_memory(&mut db1, "C");

        // Now "write it back"
        let db1_exported = db1.export().expect("Failed to export db 1").encode_to_vec();

        // First concurrent changer import and first changer removes B, adds E
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        db2.delete_memories(std::slice::from_ref(&mid_b))?;
        let (_mid_e, _bid_e) = add_test_memory(&mut db2, "E");

        // First concurrent changer is "written back" first.
        let db2_exported = db2.export().expect("Failed to export db 2").encode_to_vec();

        // Second concurrent changer import and reset.
        let mut db3 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let _ = db3.reset();

        // When db3 writeback detects that it needs a fresher copy, it will import with
        // its own changes.
        let (db3_prime, _) =
            IcingMetaDatabase::import_with_changes(tempdir(), db2_exported.as_slice(), &db3)?;

        assert_that!(
            db3_prime.get_memories_by_tag("tag", 10, PageToken::Start),
            ok((is_empty(), eq(&PageToken::Start),))
        );
        Ok(())
    }

    #[gtest]
    fn icing_delete_memory_also_deletes_views_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let mid = "memory_id".to_string();
        let views = vec![llm_view("view1", &[1.0, 0.0, 0.0]), llm_view("view2", &[0.0, 1.0, 0.0])];
        db.add_memory(&mem_with_views(&mid, &["tag"], views), 12345.to_string())?;

        assert_that!(
            db.get_view_ids_by_memory_id(mid.clone()),
            ok(unordered_elements_are![eq(&"view1"), eq(&"view2")])
        );
        db.delete_memories(std::slice::from_ref(&mid))?;
        assert_that!(db.get_view_ids_by_memory_id(mid), ok(is_empty()));
        Ok(())
    }

    #[gtest]
    fn icing_update_memory_replaces_views_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
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
    fn icing_get_memory_by_id_with_expiration_timestamp_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

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
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let mut db = IcingMetaDatabase::new(test_config())?;
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

    /// Verifies delete_memories uses MemoryId (not BlobId) for deletion.
    #[gtest]
    fn delete_memories_uses_correct_id_types_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let mid = "test_memory_id".to_string();
        let bid = "test_blob_id_12345".to_string();
        db.add_memory(
            &Memory { id: mid.clone(), tags: vec!["test_tag".into()], ..Default::default() },
            bid.clone(),
        )?;

        expect_that!(db.get_blob_id_by_memory_id(mid.clone())?, eq(&Some(bid.clone())));
        let (results, _) = db.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, contains(eq(&bid)));

        db.delete_memories(std::slice::from_ref(&mid))?;

        expect_that!(db.get_blob_id_by_memory_id(mid)?, eq(&None));
        let (results, _) = db.get_memories_by_tag("test_tag", 10, PageToken::Start)?;
        expect_that!(results, is_empty());

        Ok(())
    }

    #[gtest]
    fn get_memories_by_tag_sorts_by_created_timestamp_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

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
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let db = IcingMetaDatabase::new(test_config())?;
        let (memory_count, llm_view_count) = db.get_document_counts()?;
        expect_that!(memory_count, eq(0));
        expect_that!(llm_view_count, eq(0));
        Ok(())
    }

    #[gtest]
    fn get_document_counts_memories_only_test() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let mut db = IcingMetaDatabase::new(test_config())?;

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
        let mut db = IcingMetaDatabase::new(test_config())?;

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
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let mut db = IcingMetaDatabase::new(test_config())?;
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
        let mut db = IcingMetaDatabase::new(test_config())?;
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

    /// Verifies that `IcingMetaDatabase` is `Sync` by running concurrent reads
    /// from multiple threads against a shared instance.
    #[gtest]
    fn concurrent_reads_are_safe() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

        // Populate with test data.
        for i in 0..20 {
            let memory_id = format!("mem_{i}");
            let blob_id = format!("blob_{i}");
            db.add_memory(
                &Memory {
                    id: memory_id,
                    tags: vec!["concurrent_tag".to_string()],
                    ..Default::default()
                },
                blob_id,
            )?;
        }

        // Wrap in Arc — this requires Sync.
        let db = std::sync::Arc::new(db);

        // Spawn reader threads that concurrently query the database.
        let mut handles = Vec::new();
        for thread_idx in 0..8 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for iter in 0..100 {
                    // Concurrent tag search.
                    let (results, _) =
                        db.get_memories_by_tag("concurrent_tag", 100, PageToken::Start)?;
                    assert_that!(results, len(eq(20)));

                    // Concurrent ID lookup.
                    let mid = format!("mem_{}", (thread_idx + iter) % 20);
                    let expected_blob = format!("blob_{}", (thread_idx + iter) % 20);
                    assert_that!(db.get_blob_id_by_memory_id(mid)?, eq(&Some(expected_blob)));

                    // Concurrent get_all_memory_ids.
                    let all_ids = db.get_all_memory_ids()?;
                    assert_that!(all_ids, len(eq(20)));
                }
                Ok(())
            }));
        }

        for handle in handles {
            handle.join().expect("thread panicked")?;
        }

        Ok(())
    }

    /// Verifies that concurrent reads and writes don't crash or corrupt data.
    /// Icing's internal shared_mutex serializes writes against reads.
    #[gtest]
    fn concurrent_reads_and_writes_are_safe() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

        // Seed with initial data.
        for i in 0..10 {
            db.add_memory(
                &Memory {
                    id: format!("initial_{i}"),
                    tags: vec!["rw_tag".to_string()],
                    ..Default::default()
                },
                format!("initial_blob_{i}"),
            )?;
        }

        // Wrap in Arc<RwLock> — readers take read lock, writer takes write lock.
        let db = std::sync::Arc::new(std::sync::RwLock::new(db));

        let mut handles = Vec::new();

        // Spawn reader threads.
        for _ in 0..4 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for _ in 0..100 {
                    let guard = db.read().unwrap();
                    // Should always find at least the initial 10 memories.
                    let (results, _) =
                        guard.get_memories_by_tag("rw_tag", 100, PageToken::Start)?;
                    assert_that!(results, len(ge(10)));
                }
                Ok(())
            }));
        }

        // Spawn writer thread.
        {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for i in 0..50 {
                    let mut guard = db.write().unwrap();
                    guard.add_memory(
                        &Memory {
                            id: format!("writer_{i}"),
                            tags: vec!["rw_tag".to_string()],
                            ..Default::default()
                        },
                        format!("writer_blob_{i}"),
                    )?;
                }
                Ok(())
            }));
        }

        for handle in handles {
            handle.join().expect("thread panicked")?;
        }

        // After all threads complete, verify final state.
        let guard = db.read().unwrap();
        let (results, _) = guard.get_memories_by_tag("rw_tag", 100, PageToken::Start)?;
        // 10 initial + 50 from writer.
        assert_that!(results, len(eq(60)));

        Ok(())
    }

    /// Verifies that concurrent writes from multiple threads don't corrupt the
    /// database. Each writer adds non-overlapping memories through a RwLock.
    #[gtest]
    fn concurrent_writes_are_safe() -> anyhow::Result<()> {
        let db =
            std::sync::Arc::new(std::sync::RwLock::new(IcingMetaDatabase::new(test_config())?));

        let mut handles = Vec::new();

        // Spawn 4 writer threads, each adding 25 memories.
        for writer_idx in 0..4u32 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for i in 0..50u32 {
                    let memory_id = format!("w{writer_idx}_mem_{i}");
                    let blob_id = format!("w{writer_idx}_blob_{i}");
                    let mut guard = db.write().unwrap();
                    guard.add_memory(
                        &Memory {
                            id: memory_id,
                            tags: vec![format!("writer_{writer_idx}")],
                            ..Default::default()
                        },
                        blob_id,
                    )?;
                }
                Ok(())
            }));
        }

        for handle in handles {
            handle.join().expect("writer thread panicked")?;
        }

        // Verify all 200 memories were written correctly.
        let guard = db.read().unwrap();
        let all_ids = guard.get_all_memory_ids()?;
        assert_that!(all_ids, len(eq(200)));

        // Verify per-writer tag counts.
        for writer_idx in 0..4 {
            let (results, _) = guard.get_memories_by_tag(
                &format!("writer_{writer_idx}"),
                100,
                PageToken::Start,
            )?;
            assert_that!(results, len(eq(50)));
        }

        Ok(())
    }

    /// Stress test: many threads doing interleaved reads, writes, and deletes.
    #[gtest]
    fn stress_test_mixed_concurrent_operations() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

        // Seed with data that won't be deleted.
        for i in 0..50 {
            db.add_memory(
                &Memory {
                    id: format!("seed_{i}"),
                    tags: vec!["seed".to_string()],
                    ..Default::default()
                },
                format!("seed_blob_{i}"),
            )?;
        }

        let db = std::sync::Arc::new(std::sync::RwLock::new(db));
        let mut handles = Vec::new();

        // 6 reader threads.
        for _ in 0..6 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for _ in 0..100 {
                    let guard = db.read().unwrap();

                    // Tag search should always find the seed data.
                    let (results, _) = guard.get_memories_by_tag("seed", 200, PageToken::Start)?;
                    assert_that!(results, len(ge(50)));

                    // ID lookup for a random seed memory.
                    let idx = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .subsec_nanos() as usize
                        % 50;
                    let mid = format!("seed_{idx}");
                    assert_that!(guard.get_blob_id_by_memory_id(mid)?, some(anything()));
                }
                Ok(())
            }));
        }

        // 2 writer threads adding ephemeral memories.
        for writer_idx in 0..2 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for i in 0..50 {
                    let mut guard = db.write().unwrap();
                    guard.add_memory(
                        &Memory {
                            id: format!("stress_w{writer_idx}_{i}"),
                            tags: vec!["stress".to_string()],
                            ..Default::default()
                        },
                        format!("stress_blob_w{writer_idx}_{i}"),
                    )?;
                }
                Ok(())
            }));
        }

        // 1 deleter thread removing some of the ephemeral memories.
        {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                // Wait briefly so writers have a chance to add some data.
                std::thread::sleep(std::time::Duration::from_millis(5));
                for i in 0..25 {
                    let mut guard = db.write().unwrap();
                    // Try to delete; it may not exist yet — that's OK.
                    let _ = guard.delete_memories(&[format!("stress_w0_{i}")]);
                }
                Ok(())
            }));
        }

        for handle in handles {
            handle.join().expect("thread panicked")?;
        }

        // Verify seed data is intact.
        let guard = db.read().unwrap();
        let (seed_results, _) = guard.get_memories_by_tag("seed", 200, PageToken::Start)?;
        assert_that!(seed_results, len(eq(50)));

        Ok(())
    }

    /// Tests concurrent operations at the raw icing FFI level. All FFI methods
    /// take `&self`, so this verifies Icing's internal mutex handles truly
    /// concurrent `put` and `search` calls without Rust-side locking.
    #[gtest]
    fn concurrent_raw_icing_operations() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;

        // Seed some data.
        for i in 0..30 {
            db.add_memory(
                &Memory {
                    id: format!("raw_{i}"),
                    tags: vec!["raw_tag".to_string()],
                    name: format!("raw_name_{i}"),
                    ..Default::default()
                },
                format!("raw_blob_{i}"),
            )?;
        }

        // Share the whole IcingMetaDatabase across threads via Arc (no Mutex).
        // Since Sync is now implemented, &IcingMetaDatabase is Send.
        // Only call &self methods from threads (reads).
        let db = std::sync::Arc::new(db);

        let mut handles = Vec::new();
        for thread_idx in 0..10 {
            let db = db.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                for i in 0..100 {
                    // Concurrent get_blob_id_by_memory_id.
                    let idx = (thread_idx * 3 + i) % 30;
                    let mid = format!("raw_{idx}");
                    let expected = format!("raw_blob_{idx}");
                    assert_that!(db.get_blob_id_by_memory_id(mid)?, eq(&Some(expected)));

                    // Concurrent get_memory_by_name.
                    let name = format!("raw_name_{idx}");
                    assert_that!(db.get_memory_by_name(&name)?, some(anything()));

                    // Concurrent get_all_memory_ids.
                    let ids = db.get_all_memory_ids()?;
                    assert_that!(ids, len(eq(30)));

                    // Concurrent tag search.
                    let (results, _) = db.get_memories_by_tag("raw_tag", 100, PageToken::Start)?;
                    assert_that!(results, len(eq(30)));
                }
                Ok(())
            }));
        }

        for handle in handles {
            handle.join().expect("thread panicked")?;
        }

        Ok(())
    }

    // =========================================================================
    // mark_persisted tests
    // =========================================================================

    #[gtest]
    fn mark_persisted_clears_mutation_log() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        add_test_memory(&mut db, "1");
        add_test_memory(&mut db, "2");
        assert_that!(db.needs_writeback(), eq(true));

        db.mark_persisted();
        assert_that!(db.needs_writeback(), eq(false));
        Ok(())
    }

    #[gtest]
    fn mark_persisted_prevents_stale_rebase_replay() -> anyhow::Result<()> {
        // Simulate: add memory, persist, then rebase onto the persisted blob.
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, blob_id) = add_test_memory(&mut db, "1");
        let exported = db.export()?.encode_to_vec();

        // Simulate successful persist
        db.mark_persisted();
        assert_that!(db.needs_writeback(), eq(false));

        // Rebase onto the same blob (simulates pull_and_rebase fetching what
        // we just uploaded). With an empty mutation log, the rebase should
        // produce a clean import with no replayed operations.
        let (rebased, failed) =
            IcingMetaDatabase::import_with_changes(tempdir(), exported.as_slice(), &db)?;
        assert_eq!(failed, 0);

        // The rebased db should have the memory (from the base blob)
        // and no pending mutations.
        assert_that!(rebased.get_blob_id_by_memory_id(mem_id)?, some(eq(&blob_id)));
        assert_that!(rebased.needs_writeback(), eq(false));
        Ok(())
    }

    #[gtest]
    fn mark_persisted_does_not_affect_data() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, blob_id) = add_test_memory(&mut db, "1");
        add_test_memory(&mut db, "2");

        db.mark_persisted();

        // Data should still be accessible after clearing the mutation log.
        assert_that!(db.get_blob_id_by_memory_id(mem_id)?, some(eq(&blob_id)));
        let all_ids = db.get_all_memory_ids()?;
        assert_that!(all_ids, len(eq(2)));
        Ok(())
    }

    #[gtest]
    fn rebase_after_persist_produces_clean_state() -> anyhow::Result<()> {
        // Simulates the persist → rebase cycle that happens in
        // sync_persist_database. Without mark_persisted the rebase replays
        // stale operations (AddMemory upsert), leaving needs_writeback()
        // true and causing an infinite persist loop.
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, blob_id) = add_test_memory(&mut db, "1");
        let exported = db.export()?.encode_to_vec();

        // Simulate successful persist — clear the mutation log.
        // Removing this line causes the assertion below to fail.
        db.mark_persisted();

        // Rebase onto the blob we just persisted (simulates pull_and_rebase
        // fetching what we just uploaded).
        let (rebased, failed) =
            IcingMetaDatabase::import_with_changes(tempdir(), exported.as_slice(), &db)?;
        assert_eq!(failed, 0);

        // After persist + rebase, no pending mutations should remain.
        assert_that!(rebased.needs_writeback(), eq(false));

        // Data is intact.
        assert_that!(rebased.get_blob_id_by_memory_id(mem_id)?, some(eq(&blob_id)));
        Ok(())
    }

    // =========================================================================
    // Deferred blob delete tests
    // =========================================================================

    #[gtest]
    fn pending_blob_deletes_empty_initially() -> anyhow::Result<()> {
        let db = IcingMetaDatabase::new(test_config())?;
        assert!(db.pending_blob_deletes().is_empty());
        Ok(())
    }

    #[gtest]
    fn delete_memories_records_pending_blob_deletes() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, blob_id) = add_test_memory(&mut db, "1");
        let (mem_id_2, blob_id_2) = add_test_memory(&mut db, "2");

        db.delete_memories(&[mem_id])?;
        assert_that!(db.pending_blob_deletes(), unordered_elements_are![eq(&blob_id)]);

        db.delete_memories(&[mem_id_2])?;
        assert_that!(
            db.pending_blob_deletes(),
            unordered_elements_are![eq(&blob_id), eq(&blob_id_2)]
        );
        Ok(())
    }

    #[gtest]
    fn pending_blob_deletes_cleared_by_mark_persisted() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, _blob_id) = add_test_memory(&mut db, "1");

        db.delete_memories(&[mem_id])?;
        assert_that!(db.pending_blob_deletes(), len(eq(1)));

        // Simulates successful persist — pending deletes should be gone.
        db.mark_persisted();
        assert!(db.pending_blob_deletes().is_empty());
        Ok(())
    }

    #[gtest]
    fn rebase_remove_replay_records_pending_blob_deletes() -> anyhow::Result<()> {
        // db1: base with one memory.
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (mem_id, _blob_id) = add_test_memory(&mut db1, "1");
        let db1_exported = db1.export()?.encode_to_vec();

        // db2: concurrent session deletes the memory.
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        db2.delete_memories(std::slice::from_ref(&mem_id))?;
        assert_that!(db2.pending_blob_deletes(), len(eq(1)));

        // Rebase db2 onto db1 (memory still exists in db1's base).
        let (rebased, failed) =
            IcingMetaDatabase::import_with_changes(tempdir(), db1_exported.as_slice(), &db2)?;
        assert_eq!(failed, 0);

        // The rebased db should still have a pending blob delete.
        assert_that!(rebased.pending_blob_deletes(), len(eq(1)));

        // The memory should be gone.
        assert_that!(rebased.get_blob_id_by_memory_id(mem_id)?, none());
        Ok(())
    }

    #[gtest]
    fn rebase_add_memory_upsert_records_pending_delete_for_old_blob() -> anyhow::Result<()> {
        // db1: base with one memory.
        let mut db1 = IcingMetaDatabase::new(test_config())?;
        let (_mem_id, old_blob_id) = add_test_memory(&mut db1, "1");
        let db1_exported = db1.export()?.encode_to_vec();

        // db2: concurrent session adds memory with the same ID (upsert).
        // add_memory internally calls delete_memories for the old memory,
        // recording Remove { old_blob_id } in the mutation log.
        let mut db2 = IcingMetaDatabase::import(db1_exported.as_slice(), test_config())?;
        let new_blob_id = "new_blob_id".to_string();
        db2.add_memory(
            &Memory {
                id: "memory_id_1".to_string(),
                tags: vec!["updated_tag".to_string()],
                ..Default::default()
            },
            new_blob_id.clone(),
        )?;

        // Rebase db2 onto the original base (memory exists → upsert cleanup).
        let (rebased, failed) =
            IcingMetaDatabase::import_with_changes(tempdir(), db1_exported.as_slice(), &db2)?;
        assert_eq!(failed, 0);

        // The old blob should be pending deletion (from the Remove in the
        // upsert's mutation log).
        assert_that!(rebased.pending_blob_deletes(), unordered_elements_are![eq(&old_blob_id)]);

        // The memory should reference the new blob.
        let resolved_blob = rebased.get_blob_id_by_memory_id("memory_id_1".to_string())?;
        assert_that!(resolved_blob, some(eq(&new_blob_id)));
        Ok(())
    }

    #[gtest]
    fn delete_all_memories_records_all_pending_blob_deletes() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (_id1, blob_1) = add_test_memory(&mut db, "1");
        let (_id2, blob_2) = add_test_memory(&mut db, "2");
        let (_id3, blob_3) = add_test_memory(&mut db, "3");

        let all_ids = db.get_all_memory_ids()?;
        db.delete_memories(&all_ids)?;

        assert_that!(
            db.pending_blob_deletes(),
            unordered_elements_are![eq(&blob_1), eq(&blob_2), eq(&blob_3)]
        );
        Ok(())
    }

    #[gtest]
    fn delete_nonexistent_memory_returns_not_found_id() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let not_found = db.delete_memories(&["nonexistent_id".to_string()])?;
        assert_that!(not_found, elements_are![eq("nonexistent_id")]);
        Ok(())
    }

    #[gtest]
    fn delete_already_deleted_memory_returns_not_found_id() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, _blob_id) = add_test_memory(&mut db, "1");

        // First delete should succeed with no not-found IDs.
        let not_found = db.delete_memories(std::slice::from_ref(&mem_id))?;
        assert_that!(not_found, is_empty());

        // Second delete should report the ID as not found.
        let not_found = db.delete_memories(std::slice::from_ref(&mem_id))?;
        assert_that!(not_found, elements_are![eq(&mem_id)]);
        Ok(())
    }

    #[gtest]
    fn delete_mixed_existing_and_nonexistent_memories() -> anyhow::Result<()> {
        let mut db = IcingMetaDatabase::new(test_config())?;
        let (mem_id, _blob_id) = add_test_memory(&mut db, "1");

        let ids = vec![mem_id, "nonexistent".to_string()];
        let not_found = db.delete_memories(&ids)?;
        assert_that!(not_found, elements_are![eq("nonexistent")]);

        // The existing memory should have been deleted.
        assert_that!(db.get_all_memory_ids()?, is_empty());
        Ok(())
    }
}
