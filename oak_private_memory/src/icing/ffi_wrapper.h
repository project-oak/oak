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
class DocumentBuilder {
 public:
  DocumentBuilder() : inner_(std::make_unique<icing::lib::DocumentBuilder>()) {}

  const DocumentBuilder& SetNamespace(
      rust::Slice<const uint8_t> name_space) const {
    inner_->SetNamespace(RustSliceToString(name_space));
    return *this;
  }

  const DocumentBuilder& SetUri(rust::Slice<const uint8_t> uri) const {
    inner_->SetUri(RustSliceToString(uri));
    return *this;
  }

  const DocumentBuilder& SetKey(rust::Slice<const uint8_t> name_space,
                                rust::Slice<const uint8_t> uri) const {
    inner_->SetKey(RustSliceToString(name_space), RustSliceToString(uri));
    return *this;
  }

  const DocumentBuilder& SetSchema(rust::Slice<const uint8_t> schema) const {
    inner_->SetSchema(RustSliceToString(schema));
    return *this;
  }

  const DocumentBuilder& SetCreationTimestampMs(
      uint64_t creation_timestamp_ms) const {
    inner_->SetCreationTimestampMs(creation_timestamp_ms);
    return *this;
  }

  const DocumentBuilder& SetScore(int32_t score) const {
    inner_->SetScore(score);
    return *this;
  }

  const DocumentBuilder& AddStringProperty(
      rust::Slice<const uint8_t> name, rust::Slice<const uint8_t> value) const {
    inner_->AddStringProperty(RustSliceToString(name),
                              RustSliceToString(value));
    return *this;
  }

  const DocumentBuilder& SetTtlMs(uint64_t ttl_ms) const {
    inner_->SetTtlMs(ttl_ms);
    return *this;
  }

  const DocumentBuilder& ClearProperties() const {
    inner_->ClearProperties();
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> Build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::DocumentBuilder> inner_;
};

std::unique_ptr<DocumentBuilder> CreateDocumentBuilder();

class IcingSearchEngine {
 public:
  IcingSearchEngine(rust::Slice<const uint8_t> options);

  std::unique_ptr<std::vector<uint8_t>> Initialize() const {
    auto proto = inner_->Initialize();
    auto res = ProtoToVec(proto);
    return res;
  }

  std::unique_ptr<std::vector<uint8_t>> SetSchema(
      rust::Slice<const uint8_t> schema) const {
    icing::lib::SchemaProto proto;
    std::string slice_str = RustSliceToString(schema);
    proto.ParseFromString(slice_str);
    return ProtoToVec(inner_->SetSchema(proto));
  }

  std::unique_ptr<std::vector<uint8_t>> Put(
      rust::Slice<const uint8_t> document) const {
    icing::lib::DocumentProto proto;
    std::string slice_str = RustSliceToString(document);
    proto.ParseFromString(slice_str);
    std::string serialized_string;
    return ProtoToVec(inner_->Put(proto));
  }

  std::unique_ptr<std::vector<uint8_t>> SearchImpl(
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

  std::unique_ptr<std::vector<uint8_t>> PersistToDisk(int persist_type) const {
    return ProtoToVec(
        inner_->PersistToDisk((icing::lib::PersistType::Code)persist_type));
  }

 private:
  std::unique_ptr<icing::lib::IcingSearchEngine> inner_;
};

std::unique_ptr<IcingSearchEngine> CreateIcingSearchEngine(
    rust::Slice<const uint8_t> options);

class PropertyConfigBuilder {
 public:
  PropertyConfigBuilder()
      : inner_(std::make_unique<icing::lib::PropertyConfigBuilder>()) {}

  const PropertyConfigBuilder& SetName(rust::Slice<const uint8_t> name) const {
    inner_->SetName(RustSliceToString(name));
    return *this;
  }

  const PropertyConfigBuilder& SetDataType(int data_type) const {
    inner_->SetDataType(
        (icing::lib::PropertyConfigProto_DataType_Code)data_type);
    return *this;
  }

  const PropertyConfigBuilder& SetDataTypeString(int match_type,
                                                 int tokenizer) const {
    inner_->SetDataTypeString(
        (icing::lib::TermMatchType_Code)match_type,
        (icing::lib::StringIndexingConfig_TokenizerType_Code)tokenizer);
    return *this;
  }

  const PropertyConfigBuilder& SetDataTypeDocument(
      rust::Slice<const uint8_t> schema_type,
      bool index_nested_properties) const {
    inner_->SetDataTypeDocument(RustSliceToString(schema_type),
                                index_nested_properties);
    return *this;
  }

  const PropertyConfigBuilder& SetCardinality(int cardinality) const {
    inner_->SetCardinality(
        (icing::lib::PropertyConfigProto_Cardinality_Code)cardinality);
    return *this;
  }

  const PropertyConfigBuilder& SetDescription(
      rust::Slice<const uint8_t> description) const {
    inner_->SetDescription(RustSliceToString(description));
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> Build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::PropertyConfigBuilder> inner_;
};

// Factory function
std::unique_ptr<PropertyConfigBuilder> CreatePropertyConfigBuilder();

class SchemaTypeConfigBuilder {
 public:
  SchemaTypeConfigBuilder()
      : inner_(std::make_unique<icing::lib::SchemaTypeConfigBuilder>()) {}

  const SchemaTypeConfigBuilder& SetType(
      rust::Slice<const uint8_t> type) const {
    inner_->SetType(RustSliceToString(type));
    return *this;
  }

  const SchemaTypeConfigBuilder& AddParentType(
      rust::Slice<const uint8_t> parent_type) const {
    inner_->AddParentType(RustSliceToString(parent_type));
    return *this;
  }

  const SchemaTypeConfigBuilder& SetVersion(int32_t version) const {
    inner_->SetVersion(version);
    return *this;
  }

  const SchemaTypeConfigBuilder& SetDescription(
      rust::Slice<const uint8_t> description) const {
    inner_->SetDescription(RustSliceToString(description));
    return *this;
  }

  const SchemaTypeConfigBuilder& SetDatabase(
      rust::Slice<const uint8_t> database) const {
    inner_->SetDatabase(RustSliceToString(database));
    return *this;
  }

  const SchemaTypeConfigBuilder& AddProperty(
      const PropertyConfigBuilder& builder) const {
    auto proto_str_ptr = builder.Build();
    icing::lib::PropertyConfigProto proto;
    proto.ParseFromArray(proto_str_ptr->data(), proto_str_ptr->size());
    inner_->AddProperty(proto);
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> Build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::SchemaTypeConfigBuilder> inner_;
};

// Factory function to create an ffi::SchemaTypeConfigBuilder instance
std::unique_ptr<SchemaTypeConfigBuilder> CreateSchemaTypeConfigBuilder();

class SchemaBuilder {
 public:
  SchemaBuilder() : inner_(std::make_unique<icing::lib::SchemaBuilder>()) {}

  const SchemaBuilder& AddType(
      const SchemaTypeConfigBuilder& config_builder) const {
    auto proto_str_ptr = config_builder.Build();
    icing::lib::SchemaTypeConfigProto proto;
    proto.ParseFromArray(proto_str_ptr->data(), proto_str_ptr->size());
    inner_->AddType(proto);
    return *this;
  }

  std::unique_ptr<std::vector<uint8_t>> Build() const {
    auto built_proto = inner_->Build();
    return ProtoToVec(built_proto);
  }

 private:
  std::unique_ptr<icing::lib::SchemaBuilder> inner_;
};

std::unique_ptr<SchemaBuilder> CreateSchemaBuilder();

}  // namespace ffi
}  // namespace private_memory

}  // namespace oak
