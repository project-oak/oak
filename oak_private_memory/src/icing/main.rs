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

use icing_ffi_bridge::ffi::*;
use icing_rust_proto::icing::lib::{
    scoring_spec_proto::ranking_strategy, status_proto, term_match_type, IcingSearchEngineOptions,
    InitializeResultProto, PutResultProto, ResultSpecProto, ScoringSpecProto, SearchResultProto,
    SearchSpecProto, SetSchemaResultProto,
};
use prost::Message;

#[allow(non_snake_case)]
fn GetDefaultIcingOptions() -> IcingSearchEngineOptions {
    let mut icing_options = IcingSearchEngineOptions::default();
    icing_options.enable_scorable_properties = Some(true);
    icing_options.base_dir = Some("/tmp/icing".into());
    icing_options
}

#[allow(non_snake_case)]
fn GetDefaultScoringSpec() -> ScoringSpecProto {
    let mut scoring_spec = ScoringSpecProto::default();
    scoring_spec.rank_by = Some(ranking_strategy::Code::DocumentScore.into());
    scoring_spec
}

fn main() {
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

    let options_bytes = GetDefaultIcingOptions().encode_to_vec();
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

    let search_result_str = icing_search_engine.Search(
        &search_spec.encode_to_vec(),
        &GetDefaultScoringSpec().encode_to_vec(),
        &result_spec.encode_to_vec(),
    );
    let search_result_proto = SearchResultProto::decode(search_result_str.as_slice()).unwrap();
    let next_page_token = search_result_proto.next_page_token();
    assert!(next_page_token == 0);
    println!("Result len: {}", search_result_proto.results.len());
    assert!(search_result_proto.results.len() == 1);
}
