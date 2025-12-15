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
    create_vector_proto, embedding_indexing_config, persist_type, property_config_proto,
    scoring_spec_proto, search_spec_proto, status_proto, term_match_type, *,
};
use prost::Message;
use tempfile::tempdir;

#[cfg(test)]
mod tests {
    use icing::result_spec_proto::SnippetSpecProto;

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
        let schema = schema_builder.build().unwrap();

        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize().unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result_proto = icing_search_engine.set_schema(&schema).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = create_document_builder()
            .set_key("namespace".as_bytes(), "uri1".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property(
                "body".as_bytes(),
                &["message body one".as_bytes(), "message body two".as_bytes()],
            )
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        let result_proto = icing_search_engine.put(&doc1).unwrap();
        if result_proto.status.clone().unwrap().code != Some(status_proto::Code::Ok.into()) {
            println!("Result {:?}", result_proto);
        }
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let search_spec = SearchSpecProto {
            term_match_type: Some(term_match_type::Code::Prefix.into()),
            query: Some("one".to_string()),
            ..Default::default()
        };

        let result_spec = ResultSpecProto { num_per_page: Some(3), ..Default::default() };

        let search_result_proto = icing_search_engine
            .search(&search_spec, &get_default_scoring_spec(), &result_spec)
            .unwrap();
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
        let schema = schema_builder.build().unwrap();
        // The original database.
        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let result_proto = icing_search_engine.initialize().unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let result_proto = icing_search_engine.set_schema(&schema).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let doc1 = create_document_builder()
            .set_key("namespace".as_bytes(), "uri1".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property("body".as_bytes(), &["message body one".as_bytes()])
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        let result_proto = icing_search_engine.put(&doc1).unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));
        let result_proto = icing_search_engine.persist_to_disk(persist_type::Code::Full.into());
        let result_proto = icing::PersistToDiskResultProto::decode(result_proto.as_slice())?;
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        let ground_truth_files =
            icing::IcingGroundTruthFiles::new(temp_dir.path().to_str().unwrap())?;

        // Check the serialization
        let transformed =
            icing::IcingGroundTruthFiles::decode(&*ground_truth_files.encode_to_vec())?;
        assert_eq!(ground_truth_files, transformed);

        // Whether the database can be moved to a new directory.
        let migrated_temp_dir = tempdir().unwrap();
        let migrated_dir_str = migrated_temp_dir.path().to_str().unwrap();
        ground_truth_files.migrate(migrated_dir_str)?;
        let options_bytes = get_default_icing_options(migrated_dir_str).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        // Initialize the engine with the migrated data.
        let result_proto = icing_search_engine.initialize().unwrap();
        assert!(result_proto.status.unwrap().code == Some(status_proto::Code::Ok.into()));

        //let result_proto = icing_search_engine.set_schema(&schema);
        //assert!(result_proto.status.unwrap().code ==
        // Some(status_proto::Code::Ok.into()));

        let search_spec = SearchSpecProto {
            term_match_type: Some(term_match_type::Code::Prefix.into()),
            query: Some("one".to_string()),
            ..Default::default()
        };

        let result_spec = ResultSpecProto { num_per_page: Some(3), ..Default::default() };

        let search_result_proto = icing_search_engine
            .search(&search_spec, &get_default_scoring_spec(), &result_spec)
            .unwrap();
        let next_page_token = search_result_proto.next_page_token();
        assert!(next_page_token == 0);
        // Using assert_eq! is generally preferred over assert! for equality checks
        assert_eq!(search_result_proto.results.len(), 1);
        Ok(())
    }

    #[test]
    fn icing_embedding_search_test() {
        let temp_dir = tempdir().unwrap();

        // Define Schema
        let body_property = create_property_config_builder();
        body_property
            .set_name("body".as_bytes())
            .set_data_type_string(
                term_match_type::Code::Prefix.into(),
                string_indexing_config::tokenizer_type::Code::Plain.into(),
            )
            .set_cardinality(property_config_proto::cardinality::Code::Required.into());

        let embedding_property = create_property_config_builder();
        embedding_property
            .set_name("embedding1".as_bytes())
            .set_data_type_vector(
                embedding_indexing_config::embedding_indexing_type::Code::LinearSearch.into(),
            )
            .set_cardinality(property_config_proto::cardinality::Code::Repeated.into());

        let schema_type_builder = create_schema_type_config_builder();
        schema_type_builder
            .set_type("Message".as_bytes())
            .add_property(&body_property)
            .add_property(&embedding_property);

        let schema_builder = create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        let schema = schema_builder.build().unwrap();

        // Initialize Icing
        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let init_result = icing_search_engine.initialize().unwrap();
        assert_eq!(init_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        let set_schema_result = icing_search_engine.set_schema(&schema).unwrap();
        assert_eq!(set_schema_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        // Create Documents
        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1575492852000;
        let model_sig = "my_model_v1";

        let doc1_vectors = [
            create_vector_proto(model_sig, &[0.1, 0.2, 0.3, 0.4, 0.5]),
            create_vector_proto(model_sig, &[1.0, 2.0, 3.0, 4.0, 5.0]),
            create_vector_proto(model_sig, &[0.6, 0.7, 0.8, 0.9, -1.0]),
        ];
        let doc1 = create_document_builder()
            .set_key("namespace".as_bytes(), "uri1".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property("body".as_bytes(), &["message body one".as_bytes()])
            .add_vector_property("embedding1".as_bytes(), &doc1_vectors)
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        let doc2_vectors = [create_vector_proto(model_sig, &[-0.1, 0.2, -0.3, -0.4, 0.5])];
        let doc2 = create_document_builder()
            .set_key("namespace".as_bytes(), "uri2".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property("body".as_bytes(), &["message body two".as_bytes()])
            .add_vector_property("embedding1".as_bytes(), &doc2_vectors)
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        let doc3_vectors = [create_vector_proto(model_sig, &[-0.1, 0.2, -0.3, -0.4, 1.5])];
        let doc3 = create_document_builder()
            .set_key("namespace".as_bytes(), "uri3".as_bytes())
            .set_schema("Message".as_bytes())
            .add_string_property("body".as_bytes(), &["message body three".as_bytes()])
            .add_vector_property("embedding1".as_bytes(), &doc3_vectors)
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        // Put Documents
        let put1_result = icing_search_engine.put(&doc1).unwrap();
        assert_eq!(put1_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));
        let put2_result = icing_search_engine.put(&doc2).unwrap();
        assert_eq!(put2_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));
        let put3_result = icing_search_engine.put(&doc3).unwrap();
        assert_eq!(put3_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        // Define Search and Scoring Specs
        let mut scoring_spec = get_default_scoring_spec();
        scoring_spec.rank_by =
            Some(scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into());
        scoring_spec.advanced_scoring_expression =
            Some("sum(this.matchedSemanticScores(getEmbeddingParameter(0)))".to_string());

        let search_spec = SearchSpecProto {
            term_match_type: Some(term_match_type::Code::ExactOnly.into()),
            embedding_query_metric_type: Some(
                search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
            ),
            embedding_query_vectors: vec![create_vector_proto(
                model_sig,
                &[1.0, -1.0, -1.0, 1.0, -1.0],
            )],
            query: Some("semanticSearch(getEmbeddingParameter(0), -1)".to_string()),
            enabled_features: vec![LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()],
            ..Default::default()
        };

        let result_spec = ResultSpecProto {
            snippet_spec: Some(SnippetSpecProto {
                num_to_snippet: Some(3),
                num_matches_per_property: Some(5),
                ..Default::default()
            }),
            ..Default::default()
        };

        // Perform Search and Assert Results
        let search_result =
            icing_search_engine.search(&search_spec, &scoring_spec, &result_spec).unwrap();
        assert_eq!(search_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));
        assert_eq!(search_result.results.len(), 2);

        // Check Document 1 (uri1)
        assert_eq!(
            search_result.results[0].document.as_ref().unwrap().uri,
            Some("uri1".to_string())
        );
        // Expected score: (-0.5) + (1.0) = 0.5
        assert!((search_result.results[0].score.unwrap() - 0.5).abs() < 1e-6);

        // Check Document 2 (uri2)
        assert_eq!(
            search_result.results[1].document.as_ref().unwrap().uri,
            Some("uri2".to_string())
        );
        // Expected score: -0.9
        assert!((search_result.results[1].score.unwrap() - (-0.9)).abs() < 1e-6);
    }

    #[test]
    fn icing_embedding_search_model_aggregation_test() {
        let temp_dir = tempdir().unwrap();

        // Define Schema
        let name_property = create_property_config_builder();
        name_property
            .set_name("name".as_bytes())
            .set_data_type_string(
                term_match_type::Code::ExactOnly.into(), // Use ExactOnly for simple name matching
                string_indexing_config::tokenizer_type::Code::Plain.into(),
            )
            .set_cardinality(property_config_proto::cardinality::Code::Required.into());

        let embedding_property = create_property_config_builder();
        embedding_property
            .set_name("embeddings".as_bytes()) // Property to store our list of embeddings
            .set_data_type_vector(
                embedding_indexing_config::embedding_indexing_type::Code::LinearSearch.into(),
            )
            .set_cardinality(property_config_proto::cardinality::Code::Repeated.into());

        let schema_type_builder = create_schema_type_config_builder();
        schema_type_builder
            .set_type("CustomDoc".as_bytes())
            .add_property(&name_property)
            .add_property(&embedding_property);

        let schema_builder = create_schema_builder();
        schema_builder.add_type(&schema_type_builder);
        let schema = schema_builder.build().unwrap();

        // Initialize Icing
        let options_bytes =
            get_default_icing_options(temp_dir.path().to_str().unwrap()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let init_result = icing_search_engine.initialize().unwrap();
        assert_eq!(init_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        let set_schema_result = icing_search_engine.set_schema(&schema).unwrap();
        assert_eq!(set_schema_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        // Create Documents
        const K_DEFAULT_CREATION_TIMESTAMP_MS: u64 = 1678886400000; // Example timestamp

        // Document 1
        let doc1_embeddings = [
            create_vector_proto("test_model", &[1.0, 0.0, 0.0]), // model: "test_model"
            create_vector_proto("test_model2", &[0.0, 1.0, 0.0]), // model: "test_model2"
        ];
        let doc1 = create_document_builder()
            .set_key("ns".as_bytes(), "doc1_uri".as_bytes())
            .set_schema("CustomDoc".as_bytes())
            .add_string_property("name".as_bytes(), &["Document 1".as_bytes()])
            .add_vector_property("embeddings".as_bytes(), &doc1_embeddings)
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS)
            .build()
            .unwrap();

        // Document 2
        let doc2_embeddings = [
            create_vector_proto("test_model", &[1.0, 0.0, 0.0]), // model: "test_model"
            create_vector_proto("test_model", &[1.0, 1.0, 0.0]), // model: "test_model"
        ];
        let doc2 = create_document_builder()
            .set_key("ns".as_bytes(), "doc2_uri".as_bytes())
            .set_schema("CustomDoc".as_bytes())
            .add_string_property("name".as_bytes(), &["Document 2".as_bytes()])
            .add_vector_property("embeddings".as_bytes(), &doc2_embeddings)
            .set_creation_timestamp_ms(K_DEFAULT_CREATION_TIMESTAMP_MS + 1) // Ensure different timestamp if needed
            .build()
            .unwrap();

        // Put Documents
        let put1_result = icing_search_engine.put(&doc1).unwrap();
        assert_eq!(put1_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));
        let put2_result = icing_search_engine.put(&doc2).unwrap();
        assert_eq!(put2_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));

        // Define Search Embedding
        let search_embedding_vector = create_vector_proto("test_model", &[1.0, 1.0, 0.0]);

        // Define Search and Scoring Specs
        let mut scoring_spec = get_default_scoring_spec();
        scoring_spec.rank_by =
            Some(scoring_spec_proto::ranking_strategy::Code::AdvancedScoringExpression.into());
        // Sum of dot products for embeddings matching the search_embedding_vector's
        // model ("test_model")
        scoring_spec.advanced_scoring_expression =
            Some("sum(this.matchedSemanticScores(getEmbeddingParameter(0)))".to_string());

        let search_spec = SearchSpecProto {
            term_match_type: Some(term_match_type::Code::ExactOnly.into()), /* Not strictly
                                                                             * needed for pure
                                                                             * semantic search */
            embedding_query_metric_type: Some(
                search_spec_proto::embedding_query_metric_type::Code::DotProduct.into(),
            ),
            embedding_query_vectors: vec![search_embedding_vector], // The search query vector
            // Query to trigger semantic search. Uses the first embedding_query_vector.
            query: Some("semanticSearch(getEmbeddingParameter(0), 1.1, 3)".to_string()),
            enabled_features: vec![LIST_FILTER_QUERY_LANGUAGE_FEATURE.to_string()], /* Common feature to enable */
            ..Default::default()
        };

        let result_spec = ResultSpecProto {
            num_per_page: Some(10), // Request up to 10 results
            ..Default::default()
        };

        // Perform Search
        let search_result =
            icing_search_engine.search(&search_spec, &scoring_spec, &result_spec).unwrap();
        assert_eq!(search_result.status.unwrap().code, Some(status_proto::Code::Ok.into()));
        assert_eq!(search_result.results.len(), 1, "Expected two documents in results");

        // Assert Results
        // Score for Doc2:
        //   Embedding 1 ("test_model", [1.0, 0.0, 0.0]) dot [1.0, 1.0, 0.0] = 1.0,
        // which is not in the range [1.1, 3].   Embedding 2 ("test_model",
        // [1.0, 1.0, 0.0]) dot [1.0, 1.0, 0.0] = 2.0   Total = 2.0 = 2.0
        assert_eq!(
            search_result.results[0].document.as_ref().unwrap().uri,
            Some("doc2_uri".to_string())
        );
        assert!((search_result.results[0].score.unwrap() - 2.0).abs() < 1e-6);
    }
}
