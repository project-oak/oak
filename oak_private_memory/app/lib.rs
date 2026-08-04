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

use std::net::SocketAddr;

use serde::{Deserialize, Serialize};

mod context;
mod db_client;
mod handler;
pub mod meminfo;
mod packing;
mod persistence_worker;
pub mod service;

pub use persistence_worker::run_persistence_service;

/// The trusted sever configuration.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct ApplicationConfig {
    pub database_service_host: SocketAddr,

    /// Maximum database size in bytes. Default: 250 MB.
    #[serde(default = "default_max_database_size_bytes")]
    pub max_database_size_bytes: usize,

    /// Maximum gRPC decode message size in bytes. Default: 100 MB.
    #[serde(default = "default_max_grpc_decode_size_bytes")]
    pub max_grpc_decode_size_bytes: usize,

    /// Accepted but ignored: errors are always returned inside
    /// `SealedMemoryResponse.error` (as `google.rpc.Status`).
    ///
    /// The field is kept only so that a deployed config still setting it does
    /// not break startup — `ApplicationConfig` is `deny_unknown_fields` and
    /// `main.rs` panics on a parse failure, so removing it outright would
    /// crash-loop any server whose config has not been cleaned up yet. Delete
    /// it once no deployed config mentions it.
    #[serde(default)]
    pub default_error_propagation_in_response: bool,

    /// The blanket TTL for metadata in seconds. Default: 2 years + 1 day.
    #[serde(default = "default_blanket_ttl_seconds")]
    pub blanket_ttl_seconds: i64,

    /// The maximum allowed per-item TTL in seconds. Default: 2 years.
    #[serde(default = "default_max_memory_ttl_seconds")]
    pub max_memory_ttl_seconds: i64,

    /// When true, the embedding index uses 8-bit quantization, reducing
    /// index size with negligible recall loss. Default: false.
    #[serde(default)]
    pub enable_int8_embedding: bool,

    /// When non-empty, only memories whose `source.source_id` is in this
    /// list are accepted. Memories without a source or with an unlisted
    /// source_id are rejected with `InvalidArgument`.
    #[serde(default)]
    pub allowed_memory_sources: Vec<String>,

    /// Minimum available memory ratio required to initialize new sessions
    /// (`MemAvailable` / `MemTotal`). Rejects incoming new session
    /// handshakes with `RESOURCE_EXHAUSTED` when available RAM drops below this
    /// ratio threshold. Default: 0.05 (5%).
    #[serde(default = "default_min_available_memory_ratio")]
    pub min_available_memory_ratio: f64,
}

fn default_min_available_memory_ratio() -> f64 {
    crate::meminfo::DEFAULT_MIN_AVAILABLE_MEMORY_RATIO
}

fn default_max_database_size_bytes() -> usize {
    oak_private_memory_database::database::MAX_DATABASE_SIZE
}

fn default_max_grpc_decode_size_bytes() -> usize {
    oak_private_memory_database::database::MAX_GRPC_DECODE_SIZE
}

pub use oak_private_memory_database::clock::{
    MAX_MEMORY_TTL_SECONDS, METADATA_BLANKET_TTL_SECONDS, SECONDS_PER_DAY, SECONDS_PER_YEAR,
};

fn default_blanket_ttl_seconds() -> i64 {
    METADATA_BLANKET_TTL_SECONDS
}

fn default_max_memory_ttl_seconds() -> i64 {
    MAX_MEMORY_TTL_SECONDS
}

/// A convenience trait to convert various error types into tonic::Status.
pub(crate) trait IntoTonicResult<T>
where
    Self: Sized,
{
    /// Convert the subject into a tonic::Result<T> with the given code and
    /// message.
    fn into_tonic_result(self, code: tonic::Code, message: &str) -> tonic::Result<T>;

    /// Convert the subject into a tonic::Result<T> with Internal code and
    /// provided message.
    fn into_internal_error(self, message: &str) -> tonic::Result<T> {
        self.into_tonic_result(tonic::Code::Internal, message)
    }

    /// Convert the subject into a tonic::Result<T> with InvalidArgument code
    /// and provided message.
    fn into_invalid_argument(self, message: &str) -> tonic::Result<T> {
        self.into_tonic_result(tonic::Code::InvalidArgument, message)
    }

    /// Convert the subject into a tonic::Result<T> with FailedPrecondition code
    /// and provided message.
    fn into_failed_precondition(self, message: &str) -> tonic::Result<T> {
        self.into_tonic_result(tonic::Code::FailedPrecondition, message)
    }
}

/// Provide conversions for all Result types.
impl<T, E: core::fmt::Debug> IntoTonicResult<T> for std::result::Result<T, E> {
    fn into_tonic_result(self, code: tonic::Code, message: &str) -> tonic::Result<T> {
        self.map_err(|e| tonic::Status::new(code, format!("{message}: {e:?}")))
    }
}

/// Provide conversions for Option types.
impl<T> IntoTonicResult<T> for Option<T> {
    fn into_tonic_result(self, code: tonic::Code, message: &str) -> tonic::Result<T> {
        self.ok_or_else(|| tonic::Status::new(code, message.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn application_config_rejects_unknown_fields() {
        let json = r#"{
            "database_service_host": "127.0.0.1:8080",
            "not_a_real_field": true
        }"#;
        let result = serde_json::from_str::<ApplicationConfig>(json);
        assert!(result.is_err(), "expected deserialization to fail for unknown field");
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("not_a_real_field"),
            "error should mention the unknown field, got: {err}"
        );
    }

    #[test]
    fn application_config_default_and_custom_memory_threshold() {
        let default_json = r#"{
            "database_service_host": "127.0.0.1:8080"
        }"#;
        let config = serde_json::from_str::<ApplicationConfig>(default_json).unwrap();
        assert_eq!(
            config.min_available_memory_ratio,
            crate::meminfo::DEFAULT_MIN_AVAILABLE_MEMORY_RATIO
        );

        let custom_json = r#"{
            "database_service_host": "127.0.0.1:8080",
            "min_available_memory_ratio": 0.10
        }"#;
        let config = serde_json::from_str::<ApplicationConfig>(custom_json).unwrap();
        assert_eq!(config.min_available_memory_ratio, 0.10);
    }
}
