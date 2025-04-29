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

#[cxx::bridge(namespace = "oak::private_memory::ffi")]
mod ffi {
    // C++ types and signatures exposed to Rust.
    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type DocumentBuilder;

        fn CreateDocumentBuilder() -> UniquePtr<DocumentBuilder>;
        fn SetUri<'a>(&self, uri: &[u8]) -> &'a DocumentBuilder;
        fn SetNamespace<'a>(&self, name_space: &[u8]) -> &'a DocumentBuilder;
        fn SetKey<'a>(&self, name_space: &[u8], uri: &[u8]) -> &'a DocumentBuilder;
        fn SetSchema<'a>(&self, schema: &[u8]) -> &'a DocumentBuilder;
        fn AddStringProperty<'a>(&self, name: &[u8], value: &[u8]) -> &'a DocumentBuilder;
        fn SetCreationTimestampMs<'a>(&self, creation_timestamp_ms: u64) -> &'a DocumentBuilder;
        fn SetScore<'a>(&self, score: i32) -> &'a DocumentBuilder;
        fn SetTtlMs<'a>(&self, ttl_ms: u64) -> &'a DocumentBuilder;
        fn ClearProperties<'a>(&self) -> &'a DocumentBuilder;
        fn Build(&self) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type IcingSearchEngine;
        fn Initialize(&self) -> UniquePtr<CxxVector<u8>>;
        fn SetSchema(&self, schema: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn Put(&self, document: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn SearchImpl(
            &self,
            search_spec: &[u8],
            scoring_spec: &[u8],
            result_spec: &[u8],
        ) -> UniquePtr<CxxVector<u8>>;
        fn PersistToDisk(&self, persist_type: i32) -> UniquePtr<CxxVector<u8>>;

        fn CreateIcingSearchEngine(options: &[u8]) -> UniquePtr<IcingSearchEngine>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type SchemaBuilder; // Corresponds to ffi::SchemaBuilder

        fn CreateSchemaBuilder() -> UniquePtr<SchemaBuilder>;

        fn AddType<'a>(
            self: &'a SchemaBuilder,
            builder: &SchemaTypeConfigBuilder,
        ) -> &'a SchemaBuilder;

        fn Build(self: &SchemaBuilder) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type SchemaTypeConfigBuilder; // Corresponds to ffi::SchemaTypeConfigBuilder
        fn CreateSchemaTypeConfigBuilder() -> UniquePtr<SchemaTypeConfigBuilder>;
        fn SetType<'a>(
            self: &'a SchemaTypeConfigBuilder,
            type_name: &[u8],
        ) -> &'a SchemaTypeConfigBuilder;
        fn AddParentType<'a>(
            self: &'a SchemaTypeConfigBuilder,
            parent_type: &[u8],
        ) -> &'a SchemaTypeConfigBuilder;
        fn SetVersion<'a>(
            self: &'a SchemaTypeConfigBuilder,
            version: i32,
        ) -> &'a SchemaTypeConfigBuilder;
        fn SetDescription<'a>(
            self: &'a SchemaTypeConfigBuilder,
            description: &[u8],
        ) -> &'a SchemaTypeConfigBuilder;
        fn SetDatabase<'a>(
            self: &'a SchemaTypeConfigBuilder,
            database: &[u8],
        ) -> &'a SchemaTypeConfigBuilder;
        fn AddProperty<'a>(
            self: &'a SchemaTypeConfigBuilder,
            property_builder: &PropertyConfigBuilder,
        ) -> &'a SchemaTypeConfigBuilder;
        fn Build(self: &SchemaTypeConfigBuilder) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type PropertyConfigBuilder; // Corresponds to ffi::PropertyConfigBuilder

        fn CreatePropertyConfigBuilder() -> UniquePtr<PropertyConfigBuilder>;

        fn SetName<'a>(self: &'a PropertyConfigBuilder, name: &[u8]) -> &'a PropertyConfigBuilder;

        fn SetDataType<'a>(
            self: &'a PropertyConfigBuilder,
            data_type: i32,
        ) -> &'a PropertyConfigBuilder;

        fn SetDataTypeString<'a>(
            self: &'a PropertyConfigBuilder,
            match_type: i32,
            tokenizer: i32,
        ) -> &'a PropertyConfigBuilder;

        fn SetDataTypeDocument<'a>(
            self: &'a PropertyConfigBuilder,
            schema_type: &[u8],
            index_nested_properties: bool,
        ) -> &'a PropertyConfigBuilder;

        fn SetCardinality<'a>(
            self: &'a PropertyConfigBuilder,
            cardinality: i32,
        ) -> &'a PropertyConfigBuilder;

        fn SetDescription<'a>(
            self: &'a PropertyConfigBuilder,
            description: &[u8],
        ) -> &'a PropertyConfigBuilder;

        fn Build(self: &PropertyConfigBuilder) -> UniquePtr<CxxVector<u8>>;
    }
}

pub use ffi::*;
use icing_rust_proto::icing::lib::{
    scoring_spec_proto::ranking_strategy, status_proto, term_match_type, IcingSearchEngineOptions,
    InitializeResultProto, PutResultProto, ResultSpecProto, ScoringSpecProto, SearchResultProto,
    SearchSpecProto, SetSchemaResultProto,
};
use prost::Message;

#[allow(non_snake_case)]
impl ffi::IcingSearchEngine {
    pub fn Search(
        &self,
        search_spec: &SearchSpecProto,
        scoring_spec: &ScoringSpecProto,
        result_spec: &ResultSpecProto,
    ) -> SearchResultProto {
        let result = self.SearchImpl(
            &search_spec.encode_to_vec(),
            &scoring_spec.encode_to_vec(),
            &result_spec.encode_to_vec(),
        );
        SearchResultProto::decode(result.as_slice()).unwrap()
    }
}
