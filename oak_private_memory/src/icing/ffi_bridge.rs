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

        fn create_document_builder() -> UniquePtr<DocumentBuilder>;
        fn set_uri<'a>(&self, uri: &[u8]) -> &'a DocumentBuilder;
        fn set_namespace<'a>(&self, name_space: &[u8]) -> &'a DocumentBuilder;
        fn set_key<'a>(&self, name_space: &[u8], uri: &[u8]) -> &'a DocumentBuilder;
        fn set_schema<'a>(&self, schema: &[u8]) -> &'a DocumentBuilder;
        fn add_string_property<'a>(&self, name: &[u8], value: &[&[u8]]) -> &'a DocumentBuilder;
        fn add_int64_property<'a>(&self, name: &[u8], value: i64) -> &'a DocumentBuilder;
        fn set_creation_timestamp_ms<'a>(&self, creation_timestamp_ms: u64) -> &'a DocumentBuilder;
        fn set_score<'a>(&self, score: i32) -> &'a DocumentBuilder;
        fn set_ttl_ms<'a>(&self, ttl_ms: u64) -> &'a DocumentBuilder;
        fn clear_properties<'a>(&self) -> &'a DocumentBuilder;
        fn build_impl(&self) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type IcingSearchEngine;
        fn initialize_impl(&self) -> UniquePtr<CxxVector<u8>>;
        fn set_schema_impl(&self, schema: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn put_impl(&self, document: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn reset(&self) -> UniquePtr<CxxVector<u8>>;
        fn search_impl(
            &self,
            search_spec: &[u8],
            scoring_spec: &[u8],
            result_spec: &[u8],
        ) -> UniquePtr<CxxVector<u8>>;
        fn persist_to_disk(&self, persist_type: i32) -> UniquePtr<CxxVector<u8>>;

        fn create_icing_search_engine(options: &[u8]) -> UniquePtr<IcingSearchEngine>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type SchemaBuilder; // Corresponds to ffi::SchemaBuilder

        fn create_schema_builder() -> UniquePtr<SchemaBuilder>;

        fn add_type<'a>(
            self: &'a SchemaBuilder,
            builder: &SchemaTypeConfigBuilder,
        ) -> &'a SchemaBuilder;

        fn build_impl(self: &SchemaBuilder) -> UniquePtr<CxxVector<u8>>; // Renamed from build
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type SchemaTypeConfigBuilder; // Corresponds to ffi::SchemaTypeConfigBuilder
        fn create_schema_type_config_builder() -> UniquePtr<SchemaTypeConfigBuilder>;
        fn set_type<'a>(&'a self, type_name: &[u8]) -> &'a SchemaTypeConfigBuilder;
        fn add_parent_type<'a>(&'a self, parent_type: &[u8]) -> &'a SchemaTypeConfigBuilder;
        fn set_version<'a>(&'a self, version: i32) -> &'a SchemaTypeConfigBuilder;
        fn set_description<'a>(&'a self, description: &[u8]) -> &'a SchemaTypeConfigBuilder;
        fn set_database<'a>(&'a self, database: &[u8]) -> &'a SchemaTypeConfigBuilder;
        fn add_property<'a>(
            &'a self,
            property_builder: &PropertyConfigBuilder,
        ) -> &'a SchemaTypeConfigBuilder;
        fn build(&self) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type PropertyConfigBuilder; // Corresponds to ffi::PropertyConfigBuilder

        fn create_property_config_builder() -> UniquePtr<PropertyConfigBuilder>;

        fn set_name<'a>(&'a self, name: &[u8]) -> &'a PropertyConfigBuilder;

        fn set_data_type<'a>(&'a self, data_type: i32) -> &'a PropertyConfigBuilder;

        fn set_data_type_string<'a>(
            &'a self,
            match_type: i32,
            tokenizer: i32,
        ) -> &'a PropertyConfigBuilder;

        fn set_data_type_document<'a>(
            &'a self,
            schema_type: &[u8],
            index_nested_properties: bool,
        ) -> &'a PropertyConfigBuilder;

        fn set_cardinality<'a>(&'a self, cardinality: i32) -> &'a PropertyConfigBuilder;

        fn set_description<'a>(&'a self, description: &[u8]) -> &'a PropertyConfigBuilder;

        fn build(&self) -> UniquePtr<CxxVector<u8>>;
    }
}

// Re-export all FFI functions and types
pub use ffi::*;
use icing_rust_proto::icing::lib::{
    DocumentProto, InitializeResultProto, PutResultProto, ResultSpecProto, SchemaProto,
    ScoringSpecProto, SearchResultProto, SearchSpecProto, SetSchemaResultProto,
};
use prost::Message;

impl ffi::DocumentBuilder {
    pub fn build(&self) -> DocumentProto {
        let result = self.build_impl();
        DocumentProto::decode(result.as_slice()).unwrap()
    }
}

impl ffi::SchemaBuilder {
    pub fn build(&self) -> SchemaProto {
        let result = self.build_impl();
        SchemaProto::decode(result.as_slice()).unwrap()
    }
}

impl ffi::IcingSearchEngine {
    pub fn initialize(&self) -> InitializeResultProto {
        let result = self.initialize_impl();
        InitializeResultProto::decode(result.as_slice()).unwrap()
    }

    pub fn search(
        &self,
        search_spec: &SearchSpecProto,
        scoring_spec: &ScoringSpecProto,
        result_spec: &ResultSpecProto,
    ) -> SearchResultProto {
        let result = self.search_impl(
            // Use the snake_case FFI function name
            &search_spec.encode_to_vec(),
            &scoring_spec.encode_to_vec(),
            &result_spec.encode_to_vec(),
        );
        SearchResultProto::decode(result.as_slice()).unwrap()
    }

    pub fn set_schema(&self, schema: &SchemaProto) -> SetSchemaResultProto {
        let schema_bytes = schema.encode_to_vec();
        let result = self.set_schema_impl(&schema_bytes);
        SetSchemaResultProto::decode(result.as_slice()).unwrap()
    }

    pub fn put(&self, document: &DocumentProto) -> PutResultProto {
        let document_bytes = document.encode_to_vec();
        let result = self.put_impl(&document_bytes);
        PutResultProto::decode(result.as_slice()).unwrap()
    }
}
