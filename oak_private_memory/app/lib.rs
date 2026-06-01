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
mod packing;
mod persistence_worker;
pub mod service;

pub use persistence_worker::run_persistence_service;

/// The trusted sever configuration.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ApplicationConfig {
    pub database_service_host: SocketAddr,

    /// Maximum database size in bytes. Default: 250 MB.
    #[serde(default = "default_max_database_size_bytes")]
    pub max_database_size_bytes: usize,

    /// Maximum gRPC decode message size in bytes. Default: 100 MB.
    #[serde(default = "default_max_grpc_decode_size_bytes")]
    pub max_grpc_decode_size_bytes: usize,

    /// When true, errors are returned inside `SealedMemoryResponse.error`
    /// (as `google.rpc.Status`) by default, keeping the gRPC stream open.
    /// When false (default), errors are returned as `tonic::Status`, which
    /// may terminate the stream.
    /// The `x-error-propagation` header can still override per-request.
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
}

fn default_max_database_size_bytes() -> usize {
    250 * 1024 * 1024
}

fn default_max_grpc_decode_size_bytes() -> usize {
    100 * 1024 * 1024
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
