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
use anyhow::{bail, ensure, Context};
use external_db_client::BlobId;
use icing::{DocumentProto, IcingGroundTruthFilesHelper};
use log::debug;
use prost::Message;
use sealed_memory_rust_proto::prelude::v1::*;
use tempfile::tempdir;

use crate::MemoryId;

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
    icing_search_engine: cxx::UniquePtr<icing::IcingSearchEngine>,
    base_dir: String,
    newly_created: bool,
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

pub trait DbMigration {
    type ImportFrom;
    type ExportTo;

    /// Import from `source` to `path`.
    fn import(source: &Self::ImportFrom, path: Option<&str>) -> anyhow::Result<Self>
    where
        Self: Sized;
    fn export(&self) -> Self::ExportTo;
}

/// The generated metadata for a memory.
/// This contains the information needed to write the metadata to the icing
/// database.
struct PendingMetadata {
    icing_document: DocumentProto,
}

impl PendingMetadata {
    pub fn new(memory: &Memory, blob_id: BlobId) -> Self {
        let memory_id = &memory.id;
        let tags: Vec<&[u8]> = memory.tags.iter().map(|x| x.as_bytes()).collect();
        let embeddings: Vec<_> = memory
            .embeddings
            .iter()
            .map(|x| icing::create_vector_proto(x.identifier.as_str(), &x.values))
            .collect();
        let icing_document = icing::create_document_builder()
            .set_key(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes())
            .set_schema(SCHMA_NAME.as_bytes())
            .add_string_property(TAG_NAME.as_bytes(), &tags)
            .add_string_property(MEMORY_ID_NAME.as_bytes(), &[memory_id.as_bytes()])
            .add_string_property(BLOB_ID_NAME.as_bytes(), &[blob_id.as_bytes()])
            .add_vector_property(EMBEDDING_NAME.as_bytes(), &embeddings)
            .build();
        Self { icing_document }
    }

    pub fn document(&self) -> &DocumentProto {
        &self.icing_document
    }
}

impl IcingMetaDatabase {
    /// Creates a ResultSpecProto projection to retrieve only the blob ids.
    fn create_blob_id_projection() -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(SCHMA_NAME.to_string()),
            paths: vec![BLOB_ID_NAME.to_string()],
        }
    }

    fn extract_blob_ids_from_search_result(search_result: icing::SearchResultProto) -> Vec<BlobId> {
        search_result.results.iter().filter_map(Self::extract_blob_id_from_doc).collect::<Vec<_>>()
    }

    fn create_search_filter(path: &str) -> icing::TypePropertyMask {
        icing::TypePropertyMask {
            schema_type: Some(SCHMA_NAME.to_string()),
            paths: vec![path.to_string()],
        }
    }
    pub fn base_dir(&self) -> String {
        self.base_dir.clone()
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
            );

        let schema_builder = icing::create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        schema_builder.build()
    }

    /// Create a new icing database in `base_dir`. If there is already a icing
    /// db in `base_dir`, the old one will be deleted.
    pub fn new(base_dir: &str) -> anyhow::Result<Self> {
        let schema = Self::create_schema();

        let options_bytes = icing::get_default_icing_options(base_dir).encode_to_vec();
        let icing_search_engine = icing::create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize();
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );

        let result_proto = icing_search_engine.set_schema(&schema);
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );

        Ok(Self { icing_search_engine, base_dir: base_dir.to_string(), newly_created: true })
    }

    pub fn add_memory(&mut self, memory: &Memory, blob_id: BlobId) -> anyhow::Result<()> {
        let pending_metadata = PendingMetadata::new(memory, blob_id);
        self.add_pending_metadata(&pending_metadata)
    }

    fn add_pending_metadata(&mut self, pending_metadata: &PendingMetadata) -> anyhow::Result<()> {
        let result = self.icing_search_engine.put(pending_metadata.document());
        if result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            debug!("{:?}", result);
        }
        ensure!(
            result.status.context("no status")?.code == Some(icing::status_proto::Code::Ok.into())
        );
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
            type_property_filters: vec![Self::create_search_filter(TAG_NAME)],
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
            type_property_masks: vec![Self::create_blob_id_projection()],
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
            type_property_filters: vec![Self::create_search_filter(MEMORY_ID_NAME)],
            ..Default::default()
        };

        let result_spec = icing::ResultSpecProto {
            num_per_page: Some(1), // We expect at most one result
            type_property_masks: vec![Self::create_blob_id_projection()],
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

    pub fn reset(&self) {
        self.icing_search_engine.reset();
        let schema = Self::create_schema();
        self.icing_search_engine.set_schema(&schema);
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
        request: &SearchMemoryRequest,
    ) -> anyhow::Result<(Vec<BlobId>, Vec<f32>, PageToken)> {
        let search_query_container =
            request.query.as_ref().context("SearchMemoryRequest must contain a 'query' field")?;

        let embedding_query_details = match search_query_container.clause.as_ref() {
            Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                    eq,
                ),
            ) => eq,
            _ => bail!("SearchMemoryQuery must contain an 'EmbeddingQuery' clause"),
        };

        let query_embeddings: &[Embedding] = &embedding_query_details.embedding;
        let score_op: Option<ScoreRange> = embedding_query_details.score_range;
        let mut scoring_spec = icing::get_default_scoring_spec();
        scoring_spec.rank_by = Some(
            icing::scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into(),
        );

        // Caculate the sum of the scores of all matching embeddings.
        const SUM_ALL_MATCHING_EMBEDDING: &str =
            "sum(this.matchedSemanticScores(getEmbeddingParameter(0)))";
        scoring_spec.advanced_scoring_expression = Some(SUM_ALL_MATCHING_EMBEDDING.to_string());

        // Search the first embedding property, specified by `EMBEDDING_NAME`.
        // Since we have only one embedding property, this is the one to go.
        let query_string = if let Some(score_op) = score_op {
            let score_min = score_op.min;
            let score_max = score_op.max;
            format!("semanticSearch(getEmbeddingParameter(0), {score_min}, {score_max})")
        } else {
            "semanticSearch(getEmbeddingParameter(0))".to_string()
        };

        let search_spec = icing::SearchSpecProto {
            term_match_type: Some(icing::term_match_type::Code::ExactOnly.into()),
            embedding_query_metric_type: Some(
                icing::search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
            ),

            embedding_query_vectors: query_embeddings
                .iter()
                .map(|x| icing::create_vector_proto(x.identifier.as_str(), &x.values))
                .collect(),

            query: Some(query_string),
            enabled_features: vec![icing::LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()],
            ..Default::default()
        };
        const LIMIT: i32 = 10;
        let limit = if request.page_size > 0 { request.page_size } else { LIMIT };

        let mut result_spec =
            icing::ResultSpecProto { num_per_page: Some(limit), ..Default::default() };

        // We only need the `BlobId`.
        result_spec.type_property_masks.push(Self::create_blob_id_projection());
        let page_token = request.page_token.clone().try_into()?;
        let search_result = match page_token {
            PageToken::Start => {
                self.icing_search_engine.search(&search_spec, &scoring_spec, &result_spec)
            }
            PageToken::Token(token) => self.icing_search_engine.get_next_page(token),
            PageToken::Invalid => unreachable!(), // Already handled
        };

        if search_result.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Icing search failed for {:?}", search_result.status);
        }

        let scores: Vec<f32> = search_result
            .results
            .iter()
            .map(|x| x.score.map(|s| s as f32).context("no score"))
            .collect::<anyhow::Result<Vec<_>>>()?;
        let next_page_token =
            search_result.next_page_token.map(PageToken::from).unwrap_or(PageToken::Start);
        let blob_ids = Self::extract_blob_ids_from_search_result(search_result);
        ensure!(blob_ids.len() == scores.len());
        if blob_ids.is_empty() {
            return Ok((blob_ids, scores, PageToken::Start));
        }
        Ok((blob_ids, scores, next_page_token))
    }

    pub fn delete_memories(&mut self, memory_ids: &[MemoryId]) -> anyhow::Result<()> {
        for memory_id in memory_ids {
            let result =
                self.icing_search_engine.delete(NAMESPACE_NAME.as_bytes(), memory_id.as_bytes());
            if result.status.clone().context("no status")?.code
                != Some(icing::status_proto::Code::Ok.into())
            {
                bail!("Failed to delete memory with id {}: {:?}", memory_id, result.status);
            }
        }
        Ok(())
    }

    /// Returns true if this instance was created fresh, without any previously
    /// existing data.
    pub fn newly_created(&self) -> bool {
        self.newly_created
    }
}

impl DbMigration for IcingMetaDatabase {
    type ImportFrom = Vec<u8>;
    type ExportTo = anyhow::Result<icing::IcingGroundTruthFiles>;
    fn export(&self) -> Self::ExportTo {
        let result_proto =
            self.icing_search_engine.persist_to_disk(icing::persist_type::Code::Full.into());
        let result_proto = icing::PersistToDiskResultProto::decode(result_proto.as_slice())?;
        ensure!(
            result_proto.status.context("no status")?.code
                == Some(icing::status_proto::Code::Ok.into())
        );
        icing::IcingGroundTruthFiles::new(&self.base_dir)
    }

    /// Rebuild the icing database in `target_base_dir` given the content of the
    /// ground truth files in `buffer`.
    fn import(buffer: &Vec<u8>, target_base_dir: Option<&str>) -> anyhow::Result<Self> {
        let base_dir_str = match target_base_dir {
            Some(dir) => dir.to_string(),
            _ => {
                let temp_dir = tempdir()?;
                temp_dir.path().to_str().context("invalid temp path")?.to_string()
            }
        };
        debug!("import to {:?}", base_dir_str);

        let ground_truth = icing::IcingGroundTruthFiles::decode(buffer.as_slice())?;

        ground_truth.migrate(&base_dir_str)?;

        let options_bytes = icing::get_default_icing_options(&base_dir_str).encode_to_vec();
        let icing_search_engine = icing::create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize();
        if result_proto.status.clone().context("no status")?.code
            != Some(icing::status_proto::Code::Ok.into())
        {
            bail!("Failed to initialize Icing engine after import: {:?}", result_proto.status);
        }

        Ok(Self { icing_search_engine, base_dir: base_dir_str, newly_created: false })
    }
}

impl Drop for IcingMetaDatabase {
    fn drop(&mut self) {
        // The destructor of `icing_search_engine` will try to perform a
        // `persist_to_disk`. If the directory is deleted, a few warnings and
        // errors will be printed out. So we manually trigger its destructor
        // first, and then delete the dir.
        self.icing_search_engine = icing::icing_search_engine_null_helper();
        match std::fs::remove_dir_all(&self.base_dir) {
            Ok(()) => debug!("Successfully removed the icing directory."),
            Err(e) => debug!("Failed to remove the icing directory, {}", e),
        }
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
    use tempfile::tempdir;

    use super::*;

    #[gtest]
    fn basic_icing_search_test() -> anyhow::Result<()> {
        let temp_dir = tempdir()?;
        let mut icing_database =
            IcingMetaDatabase::new(temp_dir.path().to_str().context("invalid temp path")?)?;

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
        let temp_dir = tempdir()?;
        let base_dir = temp_dir.path().to_str().context("invalid temp path")?;
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
        let base_dir_str = icing_database.base_dir();
        let base_dir = std::path::Path::new(&base_dir_str);
        drop(icing_database); // Drop the original instance
        expect_false!(base_dir.exists());

        // Import into a new directory (or the same one after cleaning)
        let import_temp_dir = tempdir()?;
        let import_base_dir = import_temp_dir.path().to_str().context("invalid temp path")?;
        let imported_database = IcingMetaDatabase::import(&exported_data, Some(import_base_dir))?;

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
        let temp_dir = tempdir()?;
        let mut icing_database =
            IcingMetaDatabase::new(temp_dir.path().to_str().context("invalid temp path")?)?;

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
        let temp_dir = tempdir()?;
        let mut icing_database =
            IcingMetaDatabase::new(temp_dir.path().to_str().context("invalid temp path")?)?;

        let memory_id1 = "memory_embed_1".to_string();
        let blob_id1 = 98765.to_string();
        let embedding1 = Embedding {
            identifier: "test_model".to_string(),
            values: vec![1.0, 0.0, 0.0], // Vector pointing along x-axis
        };
        let memory1 = Memory {
            id: memory_id1.clone(),
            tags: vec!["embed_tag".to_string()],
            embeddings: vec![embedding1.clone()],
            ..Default::default()
        };
        icing_database.add_memory(&memory1, blob_id1.clone())?;

        let memory_id2 = "memory_embed_2".to_string();
        let blob_id2 = 98766.to_string();
        let embedding2 = Embedding {
            identifier: "test_model".to_string(),
            values: vec![0.0, 1.0, 0.0], // Vector pointing along y-axis
        };
        let memory2 = Memory {
            id: memory_id2.clone(),
            tags: vec!["embed_tag".to_string()],
            embeddings: vec![embedding2.clone()],
            ..Default::default()
        };
        icing_database.add_memory(&memory2, blob_id2.clone())?;

        let mut request = SearchMemoryRequest {
            page_size: 10,
            query: Some(sealed_memory_rust_proto::oak::private_memory::SearchMemoryQuery {
                clause: Some(sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                    sealed_memory_rust_proto::oak::private_memory::EmbeddingQuery {
                        embedding: vec![Embedding { identifier: "test_model".to_string(), values: vec![0.9, 0.1, 0.0] }],
                        ..Default::default()
                    },
                )),
            }),
            ..Default::default()
        };
        // Query embedding close to embedding1
        let (blob_ids, scores, _) = icing_database.embedding_search(&request)?;
        // Expect memory1 (blob_id1) to be the top result due to higher dot product
        assert_that!(blob_ids, elements_are![eq(&blob_id1), eq(&blob_id2)]);
        // We could also assert on the score if needed, but ordering is often sufficient
        assert_that!(scores, elements_are![eq(&0.9), eq(&0.1)]);

        request.page_size = 1;
        let (blob_ids, scores, _) = icing_database.embedding_search(&request)?;
        // Expect memory1 (blob_id1) to be the top result due to higher dot product
        assert_that!(blob_ids, elements_are![eq(&blob_id1)]);
        // We could also assert on the score if needed, but ordering is often sufficient
        assert_that!(scores, elements_are![eq(&0.9)]);
        Ok(())
    }
}
