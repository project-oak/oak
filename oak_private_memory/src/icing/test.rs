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
//

use icing::{
    ffi::*, persist_type, scoring_spec_proto::ranking_strategy, status_proto, term_match_type,
    IcingSearchEngineOptions, InitializeResultProto, PutResultProto, ResultSpecProto,
    ScoringSpecProto, SearchSpecProto, SetSchemaResultProto,
};
use prost::Message;
use tempfile::tempdir;

fn get_default_icing_options(base_dir: &str) -> IcingSearchEngineOptions {
    let mut icing_options = IcingSearchEngineOptions::default();
    icing_options.enable_scorable_properties = Some(true);
    icing_options.base_dir = Some(base_dir.to_string());
    icing_options
}

fn get_default_scoring_spec() -> ScoringSpecProto {
    let mut scoring_spec = ScoringSpecProto::default();
    scoring_spec.rank_by = Some(ranking_strategy::Code::DocumentScore.into());
    scoring_spec
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn icing_basic_search_test() {
        let temp_dir = tempdir().unwrap();
        let property_builder = CreatePropertyConfigBuilder();
        property_builder
            .SetName("body".as_bytes())
            .SetDataTypeString(2 /* TERM_MATCH_PREFIX */, 1 /* TOKENIZER_PLAIN */)
            .SetCardinality(3 /* CARDINALITY_REQUIRED */);

        let schema_type_builder = CreateSchemaTypeConfigBuilder();
        schema_type_builder.SetType("Message".as_bytes()).AddProperty(&property_builder);

        let schema_builder = CreateSchemaBuilder();
        schema_builder.AddType(&schema_type_builder);
        let schema = schema_builder.Build();

        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = CreateIcingSearchEngine(&options_bytes);
        let result = icing_search_engine.Initialize();
        let result_proto = InitializeResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result = icing_search_engine.SetSchema(schema.as_slice());
        let result_proto = SetSchemaResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = CreateDocumentBuilder()
            .SetKey("namespace".as_bytes(), &"uri1".as_bytes())
            .SetSchema("Message".as_bytes())
            .AddStringProperty("body".as_bytes(), "message body one".as_bytes())
            .SetCreationTimestampMs(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .Build();

        let result = icing_search_engine.Put(doc1.as_slice());
        let result_proto = PutResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let mut search_spec = SearchSpecProto::default();
        search_spec.term_match_type = Some(term_match_type::Code::Prefix.into());
        search_spec.query = Some("one".to_string());

        let mut result_spec = ResultSpecProto::default();
        result_spec.num_per_page = Some(3);

        let search_result_proto =
            icing_search_engine.Search(&search_spec, &get_default_scoring_spec(), &result_spec);
        let next_page_token = search_result_proto.next_page_token();
        assert!(next_page_token == 0);
        // Using assert_eq! is generally preferred over assert! for equality checks
        assert_eq!(search_result_proto.results.len(), 1);
    }

    #[test]
    fn icing_database_export_test() -> Result<(), Box<dyn std::error::Error>> {
        let temp_dir = tempdir().unwrap();
        let property_builder = CreatePropertyConfigBuilder();
        property_builder
            .SetName("body".as_bytes())
            .SetDataTypeString(2 /* TERM_MATCH_PREFIX */, 1 /* TOKENIZER_PLAIN */)
            .SetCardinality(3 /* CARDINALITY_REQUIRED */);

        let schema_type_builder = CreateSchemaTypeConfigBuilder();
        schema_type_builder.SetType("Message".as_bytes()).AddProperty(&property_builder);

        let schema_builder = CreateSchemaBuilder();
        schema_builder.AddType(&schema_type_builder);
        let schema = schema_builder.Build();

        // The original database.
        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = CreateIcingSearchEngine(&options_bytes);
        let result = icing_search_engine.Initialize();
        let result_proto = InitializeResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result = icing_search_engine.SetSchema(schema.as_slice());
        let result_proto = SetSchemaResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = CreateDocumentBuilder()
            .SetKey("namespace".as_bytes(), &"uri1".as_bytes())
            .SetSchema("Message".as_bytes())
            .AddStringProperty("body".as_bytes(), "message body one".as_bytes())
            .SetCreationTimestampMs(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .Build();

        let result = icing_search_engine.Put(doc1.as_slice());
        let result_proto = PutResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));
        icing_search_engine.PersistToDisk(persist_type::Code::Full.into());

        let ground_truth_files =
            icing::IcingGroundTruthFiles::new(temp_dir.path().to_str().unwrap())?;

        // Check the serialization
        let transformed =
            icing::IcingGroundTruthFiles::decode_from_slice(&ground_truth_files.encode_to_vec()?)?;
        assert_eq!(ground_truth_files, transformed);

        // Whether the database can be moved to a new directory.
        let migrated_temp_dir = tempdir().unwrap();
        let migrated_dir_str = migrated_temp_dir.path().to_str().unwrap();
        ground_truth_files.migrate(migrated_dir_str)?;
        let options_bytes = get_default_icing_options(migrated_dir_str).encode_to_vec();
        let icing_search_engine = CreateIcingSearchEngine(&options_bytes);

        let result = icing_search_engine.Initialize();
        let result_proto = InitializeResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result = icing_search_engine.SetSchema(schema.as_slice());
        let result_proto = SetSchemaResultProto::decode(result.as_slice()).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let mut search_spec = SearchSpecProto::default();
        search_spec.term_match_type = Some(term_match_type::Code::Prefix.into());
        search_spec.query = Some("one".to_string());

        let mut result_spec = ResultSpecProto::default();
        result_spec.num_per_page = Some(3);

        let search_result_proto =
            icing_search_engine.Search(&search_spec, &get_default_scoring_spec(), &result_spec);
        let next_page_token = search_result_proto.next_page_token();
        assert!(next_page_token == 0);
        // Using assert_eq! is generally preferred over assert! for equality checks
        assert_eq!(search_result_proto.results.len(), 1);
        Ok(())
    }
}
