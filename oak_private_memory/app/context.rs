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

use oak_private_memory_database::DatabaseWithCache;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use tonic::transport::Channel;

use crate::MessageType;

/// The state for each client connection.
pub struct UserSessionContext {
    pub dek: Vec<u8>,
    pub uid: String,
    pub message_type: MessageType,

    pub database: DatabaseWithCache,
    // This is the opaque version string received when reading in the current database.
    // It should be provided to calls that will write the database back, so that the version can be
    // checked, to prevent data loss due to concurrent database write-back.
    pub database_version: String,
    pub database_service_client: SealedMemoryDatabaseServiceClient<Channel>,
}
