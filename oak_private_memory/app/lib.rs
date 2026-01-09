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

// The message format for the plaintext.
#[derive(Default, Copy, Clone, PartialEq)]
pub enum MessageType {
    #[default]
    BinaryProto,
    Json,
}

/// The trusted sever configuration.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct ApplicationConfig {
    pub database_service_host: SocketAddr,
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
