/*
 * Copyright 2025 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This is just to test that icing can be built.
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <string>
#include <string_view>

#include "icing/document-builder.h"
#include "icing/icing-search-engine.h"
#include "icing/proto/debug.pb.h"
#include "icing/proto/document.pb.h"
#include "icing/proto/document_wrapper.pb.h"
#include "icing/proto/initialize.pb.h"
#include "icing/proto/logging.pb.h"
#include "icing/proto/optimize.pb.h"
#include "icing/proto/persist.pb.h"
#include "icing/proto/reset.pb.h"
#include "icing/proto/schema.pb.h"
#include "icing/proto/scoring.pb.h"
#include "icing/proto/search.pb.h"
#include "icing/proto/status.pb.h"
#include "icing/proto/storage.pb.h"
#include "icing/proto/term.pb.h"
#include "icing/proto/usage.pb.h"
#include "icing/schema-builder.h"
// #include "icing/testing/common-matchers.h"

namespace icing {
namespace lib {
constexpr int64_t kDefaultCreationTimestampMs = 1575492852000;
IcingSearchEngineOptions GetDefaultIcingOptions() {
  IcingSearchEngineOptions icing_options;
  icing_options.set_enable_scorable_properties(true);
  icing_options.set_base_dir("/tmp/icing");
  // icing_options.set_calculate_time_since_last_attempted_optimize(true);
  // icing_options.set_enable_qualified_id_join_index_v3(true);
  // icing_options.set_enable_delete_propagation_from(false);
  // icing_options.set_enable_marker_file_for_optimize(true);
  return icing_options;
}

ScoringSpecProto GetDefaultScoringSpec() {
  ScoringSpecProto scoring_spec;
  scoring_spec.set_rank_by(ScoringSpecProto::RankingStrategy::DOCUMENT_SCORE);
  return scoring_spec;
}

void gogo() {
  SchemaProto schema =
      SchemaBuilder()
          .AddType(SchemaTypeConfigBuilder().SetType("Message").AddProperty(
              PropertyConfigBuilder()
                  .SetName("body")
                  .SetDataTypeString(TERM_MATCH_PREFIX, TOKENIZER_PLAIN)
                  .SetCardinality(CARDINALITY_REQUIRED)))
          .Build();

  DocumentProto document1 =
      DocumentBuilder()
          .SetKey("namespace", "uri1")
          .SetSchema("Message")
          .AddStringProperty("body", "message body one")
          .SetCreationTimestampMs(kDefaultCreationTimestampMs)
          .Build();
  DocumentProto document2 =
      DocumentBuilder()
          .SetKey("namespace", "uri2")
          .SetSchema("Message")
          .AddStringProperty("body", "message body two")
          .SetCreationTimestampMs(kDefaultCreationTimestampMs)
          .Build();

  DocumentProto document3 =
      DocumentBuilder()
          .SetKey("namespace", "uri3")
          .SetSchema("Message")
          .AddStringProperty("body", "message body three")
          .SetCreationTimestampMs(kDefaultCreationTimestampMs)
          .Build();

  IcingSearchEngine icing(GetDefaultIcingOptions());
  assert(icing.Initialize().status().code() == StatusProto::OK);

  assert(icing.SetSchema(schema).status().code() == StatusProto::OK);

  assert(icing.Put(document1).status().code() == StatusProto::OK);
  assert(icing.Put(document2).status().code() == StatusProto::OK);
  assert(icing.Put(document3).status().code() == StatusProto::OK);
  icing.PersistToDisk(PersistType::FULL);

  SearchSpecProto search_spec;
  search_spec.set_term_match_type(TermMatchType::PREFIX);
  search_spec.set_query("two");

  ResultSpecProto result_spec;
  result_spec.set_num_per_page(3);

  // Searches and gets the first page, 1 result
  SearchResultProto expected_search_result_proto;
  expected_search_result_proto.mutable_status()->set_code(StatusProto::OK);
  *expected_search_result_proto.mutable_results()->Add()->mutable_document() =
      document2;
  SearchResultProto search_result_proto =
      icing.Search(search_spec, GetDefaultScoringSpec(), result_spec);
  uint64_t next_page_token = search_result_proto.next_page_token();
  search_result_proto.set_next_page_token(next_page_token);
  assert(next_page_token == 0);
  assert(search_result_proto.results().size() == 1);
  expected_search_result_proto.set_next_page_token(next_page_token);
}
}  // namespace lib
}  // namespace icing

int main(int argc, char** argv) {
  icing::lib::gogo();
  return 0;
}
