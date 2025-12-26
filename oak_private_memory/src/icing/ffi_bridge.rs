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
        fn set_uri(&self, uri: &[u8]) -> &DocumentBuilder;
        fn set_namespace(&self, name_space: &[u8]) -> &DocumentBuilder;
        fn set_key(&self, name_space: &[u8], uri: &[u8]) -> &DocumentBuilder;
        fn set_schema(&self, schema: &[u8]) -> &DocumentBuilder;
        fn add_string_property(&self, name: &[u8], value: &[&[u8]]) -> &DocumentBuilder;
        fn add_vector_property_impl(&self, name: &[u8], value: &[&[u8]]) -> &DocumentBuilder;
        fn add_int64_property(&self, name: &[u8], value: i64) -> &DocumentBuilder;
        fn set_creation_timestamp_ms(&self, creation_timestamp_ms: u64) -> &DocumentBuilder;
        fn set_score(&self, score: i32) -> &DocumentBuilder;
        fn set_ttl_ms(&self, ttl_ms: u64) -> &DocumentBuilder;
        fn clear_properties(&self) -> &DocumentBuilder;
        fn build_impl(&self) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");

        type IcingSearchEngine;
        fn initialize_impl(&self) -> UniquePtr<CxxVector<u8>>;
        fn set_schema_impl(&self, schema: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn put_impl(&self, document: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn delete_impl(&self, ns: &[u8], uri: &[u8]) -> UniquePtr<CxxVector<u8>>;
        fn get_next_page_impl(&self, next_page_token: u64) -> UniquePtr<CxxVector<u8>>;
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

        fn set_data_type_vector(&self, data_type_vector: i32) -> &PropertyConfigBuilder;
        fn set_data_type_string<'a>(
            &'a self,
            match_type: i32,
            tokenizer: i32,
        ) -> &'a PropertyConfigBuilder;
        fn set_data_type_int64<'a>(&'a self, value: i32) -> &'a PropertyConfigBuilder;

        fn set_data_type_document<'a>(
            &'a self,
            schema_type: &[u8],
            index_nested_properties: bool,
        ) -> &'a PropertyConfigBuilder;

        fn set_cardinality<'a>(&'a self, cardinality: i32) -> &'a PropertyConfigBuilder;

        fn set_description<'a>(&'a self, description: &[u8]) -> &'a PropertyConfigBuilder;

        fn build(&self) -> UniquePtr<CxxVector<u8>>;
    }

    unsafe extern "C++" {
        include!("src/icing/ffi_wrapper.h");
        fn set_logging(enabled: bool) -> bool;
    }
}

use cxx::UniquePtr;
// Re-export all FFI functions and types
pub use ffi::*;
use icing_rust_proto::icing::lib::{
    property_proto::VectorProto, DeleteResultProto, DocumentProto, InitializeResultProto,
    PutResultProto, ResultSpecProto, SchemaProto, ScoringSpecProto, SearchResultProto,
    SearchSpecProto, SetSchemaResultProto,
};
use prost::Message;

impl ffi::DocumentBuilder {
    pub fn build(&self) -> anyhow::Result<DocumentProto> {
        let result = self.build_impl();
        Ok(DocumentProto::decode(result.as_slice())?)
    }

    pub fn add_vector_property(&self, name: &[u8], values: &[VectorProto]) -> &Self {
        let value_strs: Vec<Vec<u8>> = values.iter().map(|s| s.encode_to_vec()).collect();
        let value_strs_ref: Vec<&[u8]> = value_strs.iter().map(|s| s.as_slice()).collect();
        self.add_vector_property_impl(name, &value_strs_ref);
        self
    }
}

impl ffi::SchemaBuilder {
    pub fn build(&self) -> anyhow::Result<SchemaProto> {
        let result = self.build_impl();
        Ok(SchemaProto::decode(result.as_slice())?)
    }
}

impl ffi::IcingSearchEngine {
    pub fn initialize(&self) -> anyhow::Result<InitializeResultProto> {
        let result = self.initialize_impl();
        Ok(InitializeResultProto::decode(result.as_slice())?)
    }

    pub fn search(
        &self,
        search_spec: &SearchSpecProto,
        scoring_spec: &ScoringSpecProto,
        result_spec: &ResultSpecProto,
    ) -> anyhow::Result<SearchResultProto> {
        let result = self.search_impl(
            // Use the snake_case FFI function name
            &search_spec.encode_to_vec(),
            &scoring_spec.encode_to_vec(),
            &result_spec.encode_to_vec(),
        );
        Ok(SearchResultProto::decode(result.as_slice())?)
    }

    pub fn set_schema(&self, schema: &SchemaProto) -> anyhow::Result<SetSchemaResultProto> {
        let schema_bytes = schema.encode_to_vec();
        let result = self.set_schema_impl(&schema_bytes);
        Ok(SetSchemaResultProto::decode(result.as_slice())?)
    }

    pub fn put(&self, document: &DocumentProto) -> anyhow::Result<PutResultProto> {
        let document_bytes = document.encode_to_vec();
        let result = self.put_impl(&document_bytes);
        Ok(PutResultProto::decode(result.as_slice())?)
    }

    pub fn delete(&self, namespace: &[u8], uri: &[u8]) -> anyhow::Result<DeleteResultProto> {
        let result = self.delete_impl(namespace, uri);
        Ok(DeleteResultProto::decode(result.as_slice())?)
    }

    pub fn get_next_page(&self, next_page_token: u64) -> anyhow::Result<SearchResultProto> {
        let result = self.get_next_page_impl(next_page_token);
        Ok(SearchResultProto::decode(result.as_slice())?)
    }
}

// Useful constants from icing

pub const LIST_FILTER_QUERY_LANGUAGE_FEATURE: &str = "LIST_FILTER_QUERY_LANGUAGE";
pub const HAS_PROPERTY_FUNCTION_FEATURE: &str = "HAS_PROPERTY_FUNCTION";

pub fn icing_search_engine_null_helper() -> UniquePtr<IcingSearchEngine> {
    UniquePtr::null()
}
