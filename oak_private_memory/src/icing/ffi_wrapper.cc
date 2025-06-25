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

#include "ffi_wrapper.h"

#include <algorithm>
#include <functional>
#include <set>
#include <string>
#include <unordered_map>

#include "icing/proto/initialize.pb.h"
#include "src/icing/ffi_bridge.rs.h"

namespace oak {
namespace private_memory {
namespace ffi {

std::string RustSliceToString(const rust::Slice<const uint8_t>& slice) {
  return std::string(reinterpret_cast<const char*>(slice.data()), slice.size());
}

std::unique_ptr<DocumentBuilder> create_document_builder() {
  return std::make_unique<DocumentBuilder>();
}

IcingSearchEngine::IcingSearchEngine(rust::Slice<const uint8_t> options) {
  icing::lib::IcingSearchEngineOptions options_proto;
  std::string options_str = RustSliceToString(options);
  options_proto.ParseFromString(options_str);
  inner_ = std::make_unique<icing::lib::IcingSearchEngine>(options_proto);
}

std::unique_ptr<IcingSearchEngine> create_icing_search_engine(
    rust::Slice<const uint8_t> options) {
  return std::make_unique<IcingSearchEngine>(options);
}

std::unique_ptr<SchemaTypeConfigBuilder> create_schema_type_config_builder() {
  return std::make_unique<SchemaTypeConfigBuilder>();
}

std::unique_ptr<SchemaBuilder> create_schema_builder() {
  return std::make_unique<SchemaBuilder>();
}

std::unique_ptr<PropertyConfigBuilder> create_property_config_builder() {
  return std::make_unique<PropertyConfigBuilder>();
}

bool set_logging(bool enabled) {
  if (enabled) {
    return icing::lib::SetLoggingLevel(icing::lib::LogSeverity::INFO);
  } else {
    return icing::lib::SetLoggingLevel(icing::lib::LogSeverity::FATAL);
  }
}

}  // namespace ffi

}  // namespace private_memory
}  // namespace oak
