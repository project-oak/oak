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

pub mod v1 {
    pub use crate::oak::private_memory::{
        AddMemoryRequest, AddMemoryResponse, DataBlob, DeleteMemoryRequest, DeleteMemoryResponse,
        Embedding, EmbeddingQuery, EmbeddingQueryMetricType, EncryptedDataBlob,
        EncryptedMetadataBlob, EncryptedUserInfo, GetMemoriesByIdRequest, GetMemoriesByIdResponse,
        GetMemoriesRequest, GetMemoriesResponse, GetMemoryByIdRequest, GetMemoryByIdResponse,
        InvalidRequestResponse, KeyDerivationInfo, KeySyncRequest, KeySyncResponse, Memory,
        MemoryContent, MemoryField, MemoryValue, PlainTextUserInfo, ResetMemoryRequest,
        ResetMemoryResponse, ResultMask, ScoreRange, SealedMemoryCredentials, SealedMemoryRequest,
        SealedMemoryResponse, SealedMemorySessionRequest, SealedMemorySessionResponse,
        SearchMemoryQuery, SearchMemoryRequest, SearchMemoryResponse, SearchMemoryResultItem,
        UserDb, UserRegistrationRequest, UserRegistrationResponse, WrappedDataEncryptionKey,
        key_sync_response, memory_value, sealed_memory_request, sealed_memory_response,
        search_memory_query, user_registration_response,
    };
}
