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

#pragma once
#include <iostream>
#include <memory>
#include <string>

#include "icing/document-builder.h"
#include "icing/icing-search-engine.h"
#include "icing/schema-builder.h"
#include "rust/cxx.h"

namespace oak {
namespace private_memory {
namespace ffi {
template <typename ProtoT>
std::unique_ptr<std::vector<uint8_t>> ProtoToVec(ProtoT proto) {
  size_t nbytes = proto.ByteSizeLong();
  std::unique_ptr<std::vector<uint8_t>> result =
      std::make_unique<std::vector<uint8_t>>(std::vector<uint8_t>(nbytes, 0));
  proto.SerializeToArray(result->data(), nbytes);
  return result;
}
std::string RustSliceToString(const rust::Slice<const uint8_t>& slice);

// The max number of argumets that can be passed in `AddStringProperty`.
constexpr size_t kMaxValuesNum = 128;
// Icing's DocumentBuilder has the following signature for AddStringProperty
// ```
// template <typename... V>
// DocumentBuilder& AddStringProperty(std::string property_name,
//                                    V... string_values) {
// return AddStringProperty(std::move(property_name), {string_values...});
// }
// ```
//
// However, Rust doesn't support vardiac function calls. We need to use the
// following template tricks to unpack a vector of string statically.
//
// To avoid infinite recursion, we bound the number of arguments by
// `kMaxValuesNum`.
template <typename BuilderType, typename... V>
inline void RecursivelyAddString(
    BuilderType& builder, std::string name,
    rust::Slice<const rust::Slice<const uint8_t>> values, V... string_values) {
  if (values.empty()) {
    builder.AddStringProperty(name, string_values...);
  } else {
    std::string tail = RustSliceToString(values.back());
    rust::Slice<const rust::Slice<const uint8_t>> new_values(values.data(),
                                                             values.size() - 1);
    if constexpr (sizeof...(V) < kMaxValuesNum) {
      RecursivelyAddString(builder, std::move(name), new_values,
                           std::move(tail), std::move(string_values)...);
    }
  }
}

template <typename BuilderType, typename... V>
inline void RecursivelyAddVector(
    BuilderType& builder, std::string name,
    rust::Slice<const rust::Slice<const uint8_t>> values, V... proto_values) {
  if (values.empty()) {
    builder.AddVectorProperty(name, proto_values...);
  } else {
    icing::lib::PropertyProto::VectorProto proto;
    proto.ParseFromArray(values.back().data(), values.back().size());
    rust::Slice<const rust::Slice<const uint8_t>> new_values(values.data(),
                                                             values.size() - 1);
    if constexpr (sizeof...(V) < kMaxValuesNum) {
      RecursivelyAddVector(builder, std::move(name), new_values,
                           std::move(proto), std::move(proto_values)...);
    }
  }
}

class DocumentBuilder {
 public:
  DocumentBuilder() : inner_(std::make_unique<icing::lib::DocumentBuilder>()) {}

  const DocumentBuilder& set_namespace(
      rust::Slice<const uint8_t> name_space) const {
    inner_->SetNamespace(RustSliceToString(name_space));
    return *this;
  }

  const DocumentBuilder& set_uri(rust::Slice<const uint8_t> uri) const {
    inner_->SetUri(RustSliceToString(uri));
    return *this;
  }

  const DocumentBuilder& set_key(rust::Slice<const uint8_t> name_space,
                                 rust::Slice<const uint8_t> uri) const {
    inner_->SetKey(RustSliceToString(name_space), RustSliceToString(uri));
    return *this;
  }

  const DocumentBuilder& set_schema(rust::Slice<const uint8_t> schema) const {
    inner_->SetSchema(RustSliceToString(schema));
    return *this;
  }

  const DocumentBuilder& set_creation_timestamp_ms(
      uint64_t creation_timestamp_ms) const {
    inner_->SetCreationTimestampMs(creation_timestamp_ms);
    return *this;
  }

  const DocumentBuilder& set_score(int32_t score) const {
    inner_->SetScore(score);
    return *this;
  }

  const DocumentBuilder& add_string_property(
      rust::Slice<const uint8_t> name,
      rust::Slice<const rust::Slice<const uint8_t>> value) const {
    RecursivelyAddString(*inner_, RustSliceToString(name), value);
    return *this;
  }

  const DocumentBuilder& add_vector_property_impl(
      rust::Slice<const uint8_t> name,
      rust::Slice<const rust::Slice<const uint8_t>> value) const {
    RecursivelyAddVector(*inner_, RustSliceToString(name), value);
    return *this;
  }

  const DocumentBuilder& add_int64_property(rust::Slice<const uint8_t> name,
                                            int64_t value) const {
    inner_->AddInt64Property(RustSliceToString(name), value);
    return *this;
  }

  const DocumentBuilder& set_ttl_ms(uint64_t ttl_ms) const {
    inner_->SetTtlMs(ttl_ms);
    return *this;
  }

  const DocumentBuilder& clear_properties() const {
    inner_->ClearProperties();
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> build_impl() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::DocumentBuilder> inner_;
};

std::unique_ptr<DocumentBuilder> create_document_builder();

class IcingSearchEngine {
 public:
  IcingSearchEngine(rust::Slice<const uint8_t> options);

  std::unique_ptr<std::vector<uint8_t>> initialize_impl() const {
    auto proto = inner_->Initialize();
    auto res = ProtoToVec(proto);
    return res;
  }

  std::unique_ptr<std::vector<uint8_t>> reset() const {
    auto proto = inner_->Reset();
    auto res = ProtoToVec(proto);
    return res;
  }

  std::unique_ptr<std::vector<uint8_t>> set_schema_impl(
      rust::Slice<const uint8_t> schema) const {
    icing::lib::SchemaProto proto;
    std::string slice_str = RustSliceToString(schema);
    proto.ParseFromString(slice_str);
    return ProtoToVec(inner_->SetSchema(proto));
  }

  std::unique_ptr<std::vector<uint8_t>> put_impl(
      rust::Slice<const uint8_t> document) const {
    icing::lib::DocumentProto proto;
    std::string slice_str = RustSliceToString(document);
    proto.ParseFromString(slice_str);
    std::string serialized_string;
    return ProtoToVec(inner_->Put(proto));
  }

  std::unique_ptr<std::vector<uint8_t>> delete_impl(
      rust::Slice<const uint8_t> ns, rust::Slice<const uint8_t> uri) const {
    std::string namespace_str = RustSliceToString(ns);
    std::string uri_str = RustSliceToString(uri);
    return ProtoToVec(inner_->Delete(namespace_str, uri_str));
  }

  // NOTE: There will be a new API that accepts a proto instead of a uint64_t,
  // but they are not available in the OSS yet.
  std::unique_ptr<std::vector<uint8_t>> get_next_page_impl(
      std::uint64_t next_page_token) const {
    return ProtoToVec(inner_->GetNextPage(next_page_token));
  }

  std::unique_ptr<std::vector<uint8_t>> search_impl(
      rust::Slice<const uint8_t> search_spec,
      rust::Slice<const uint8_t> scoring_spec,
      rust::Slice<const uint8_t> result_spec) const {
    icing::lib::SearchSpecProto search_proto;
    icing::lib::ScoringSpecProto scoring_proto;
    icing::lib::ResultSpecProto result_proto;
    search_proto.ParseFromString(RustSliceToString(search_spec));
    scoring_proto.ParseFromString(RustSliceToString(scoring_spec));
    result_proto.ParseFromString(RustSliceToString(result_spec));

    return ProtoToVec(
        inner_->Search(search_proto, scoring_proto, result_proto));
  }

  std::unique_ptr<std::vector<uint8_t>> persist_to_disk(
      int persist_type) const {
    return ProtoToVec(
        inner_->PersistToDisk((icing::lib::PersistType::Code)persist_type));
  }

 private:
  std::unique_ptr<icing::lib::IcingSearchEngine> inner_;
};

std::unique_ptr<IcingSearchEngine> create_icing_search_engine(
    rust::Slice<const uint8_t> options);

class PropertyConfigBuilder {
 public:
  PropertyConfigBuilder()
      : inner_(std::make_unique<icing::lib::PropertyConfigBuilder>()) {}

  const PropertyConfigBuilder& set_name(rust::Slice<const uint8_t> name) const {
    inner_->SetName(RustSliceToString(name));
    return *this;
  }

  const PropertyConfigBuilder& set_data_type(int data_type) const {
    inner_->SetDataType(
        (icing::lib::PropertyConfigProto_DataType_Code)data_type);
    return *this;
  }

  const PropertyConfigBuilder& set_data_type_int64(int32_t value) const {
    inner_->SetDataTypeInt64(
        static_cast<icing::lib::IntegerIndexingConfig_NumericMatchType_Code>(
            value));
    return *this;
  }

  const PropertyConfigBuilder& set_data_type_vector(int data_type) const {
    inner_->SetDataTypeVector(
        (icing::lib::EmbeddingIndexingConfig::EmbeddingIndexingType::Code)
            data_type);
    return *this;
  }

  const PropertyConfigBuilder& set_data_type_string(int match_type,
                                                    int tokenizer) const {
    inner_->SetDataTypeString(
        (icing::lib::TermMatchType_Code)match_type,
        (icing::lib::StringIndexingConfig_TokenizerType_Code)tokenizer);
    return *this;
  }

  const PropertyConfigBuilder& set_data_type_document(
      rust::Slice<const uint8_t> schema_type,
      bool index_nested_properties) const {
    inner_->SetDataTypeDocument(RustSliceToString(schema_type),
                                index_nested_properties);
    return *this;
  }

  const PropertyConfigBuilder& set_cardinality(int cardinality) const {
    inner_->SetCardinality(
        (icing::lib::PropertyConfigProto_Cardinality_Code)cardinality);
    return *this;
  }

  const PropertyConfigBuilder& set_description(
      rust::Slice<const uint8_t> description) const {
    inner_->SetDescription(RustSliceToString(description));
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::PropertyConfigBuilder> inner_;
};

// Factory function
std::unique_ptr<PropertyConfigBuilder> create_property_config_builder();

class SchemaTypeConfigBuilder {
 public:
  SchemaTypeConfigBuilder()
      : inner_(std::make_unique<icing::lib::SchemaTypeConfigBuilder>()) {}

  const SchemaTypeConfigBuilder& set_type(
      rust::Slice<const uint8_t> type) const {
    inner_->SetType(RustSliceToString(type));
    return *this;
  }

  const SchemaTypeConfigBuilder& add_parent_type(
      rust::Slice<const uint8_t> parent_type) const {
    inner_->AddParentType(RustSliceToString(parent_type));
    return *this;
  }

  const SchemaTypeConfigBuilder& set_version(int32_t version) const {
    inner_->SetVersion(version);
    return *this;
  }

  const SchemaTypeConfigBuilder& set_description(
      rust::Slice<const uint8_t> description) const {
    inner_->SetDescription(RustSliceToString(description));
    return *this;
  }

  const SchemaTypeConfigBuilder& set_database(
      rust::Slice<const uint8_t> database) const {
    inner_->SetDatabase(RustSliceToString(database));
    return *this;
  }

  const SchemaTypeConfigBuilder& add_property(
      const PropertyConfigBuilder& builder) const {
    auto proto_str_ptr = builder.build();
    icing::lib::PropertyConfigProto proto;
    proto.ParseFromArray(proto_str_ptr->data(), proto_str_ptr->size());
    inner_->AddProperty(proto);
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::SchemaTypeConfigBuilder> inner_;
};

// Factory function to create an ffi::SchemaTypeConfigBuilder instance
std::unique_ptr<SchemaTypeConfigBuilder> create_schema_type_config_builder();

class SchemaBuilder {
 public:
  SchemaBuilder() : inner_(std::make_unique<icing::lib::SchemaBuilder>()) {}

  const SchemaBuilder& add_type(
      const SchemaTypeConfigBuilder& config_builder) const {
    auto proto_str_ptr = config_builder.build();
    icing::lib::SchemaTypeConfigProto proto;
    proto.ParseFromArray(proto_str_ptr->data(), proto_str_ptr->size());
    inner_->AddType(proto);
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> build_impl() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::SchemaBuilder> inner_;
};

std::unique_ptr<SchemaBuilder> create_schema_builder();

// Logging related functions

// If `enabled` is true, logging will be enabled at INFO level. Otherwise,
// logging will be enabled at FATAL level.
bool set_logging(bool enabled);

}  // namespace ffi
}  // namespace private_memory

}  // namespace oak
