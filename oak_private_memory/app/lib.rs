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
