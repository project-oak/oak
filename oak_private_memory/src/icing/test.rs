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

use icing::{persist_type, status_proto, term_match_type, *};
use prost::Message;
use tempfile::tempdir;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn icing_basic_search_test() {
        let temp_dir = tempdir().unwrap();
        let property_builder = create_property_config_builder();
        property_builder
            .set_name("body".as_bytes())
            .set_data_type_string(
                term_match_type::Code::Prefix.into(),
                1, /* TOKENIZER_PLAIN */
            )
            .set_cardinality(property_config_proto::cardinality::Code::Repeated.into());

        let schema_type_builder = create_schema_type_config_builder();
        schema_type_builder.set_type("Message".as_bytes()).add_property(&property_builder);

        let schema_builder = create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        let schema = schema_builder.build();

        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result_proto = icing_search_engine.set_schema(&schema);
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = create_document_builder()
            .set_key("namespace".as_bytes(), &"uri1".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property(
                "body".as_bytes(),
                &["message body one".as_bytes(), "message body two".as_bytes()],
            )
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build();

        let result_proto = icing_search_engine.put(&doc1);
        if result_proto.status.clone().unwrap().code != Some(status_proto::Code::Ok.into()) {
            println!("Result {:?}", result_proto);
        }
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let mut search_spec = SearchSpecProto::default();
        search_spec.term_match_type = Some(term_match_type::Code::Prefix.into());
        search_spec.query = Some("one".to_string());

        let mut result_spec = ResultSpecProto::default();
        result_spec.num_per_page = Some(3);

        let search_result_proto =
            icing_search_engine.search(&search_spec, &get_default_scoring_spec(), &result_spec);
        let next_page_token = search_result_proto.next_page_token();
        assert!(next_page_token == 0);
        // Using assert_eq! is generally preferred over assert! for equality checks
        assert_eq!(search_result_proto.results.len(), 1);
    }

    #[test]
    fn icing_database_export_test() -> Result<(), Box<dyn std::error::Error>> {
        let temp_dir = tempdir().unwrap();
        let property_builder = create_property_config_builder();
        property_builder
            .set_name("body".as_bytes())
            .set_data_type_string(
                term_match_type::Code::Prefix.into(),
                1, /* TOKENIZER_PLAIN */
            )
            .set_cardinality(3 /* CARDINALITY_REQUIRED */);

        let schema_type_builder = create_schema_type_config_builder();
        schema_type_builder.set_type("Message".as_bytes()).add_property(&property_builder);

        let schema_builder = create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        let schema = schema_builder.build();
        // The original database.
        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result_proto = icing_search_engine.set_schema(&schema);
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = create_document_builder()
            .set_key("namespace".as_bytes(), &"uri1".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property("body".as_bytes(), &["message body one".as_bytes()])
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build();

        let result_proto = icing_search_engine.put(&doc1);
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));
        icing_search_engine.persist_to_disk(persist_type::Code::Full.into());

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
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        // Initialize the engine with the migrated data.
        let result_proto = icing_search_engine.initialize();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        //let result_proto = icing_search_engine.set_schema(&schema);
        //assert!(result_proto.status.unwrap().code ==
        // Some(status_proto::Code::Ok.into()));

        let mut search_spec = SearchSpecProto::default();
        search_spec.term_match_type = Some(term_match_type::Code::Prefix.into());
        search_spec.query = Some("one".to_string());

        let mut result_spec = ResultSpecProto::default();
        result_spec.num_per_page = Some(3);

        let search_result_proto =
            icing_search_engine.search(&search_spec, &get_default_scoring_spec(), &result_spec);
        let next_page_token = search_result_proto.next_page_token();
        assert!(next_page_token == 0);
        // Using assert_eq! is generally preferred over assert! for equality checks
        assert_eq!(search_result_proto.results.len(), 1);
        Ok(())
    }
}
