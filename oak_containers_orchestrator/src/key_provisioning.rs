//
// Copyright 2023 The Project Oak Authors
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

use crate::{
    crypto::KeyStore,
    proto::oak::{
        containers::v1::{
            orchestrator_key_provisioning_server::OrchestratorKeyProvisioning, SendGroupKeysRequest,
        },
        key_provisioning::v1::{
            key_provisioning_server::KeyProvisioning, GetGroupKeysRequest, GetGroupKeysResponse,
        },
    },
};
use std::sync::{Arc, OnceLock};
use tonic::{Request, Response};

struct KeyProvisioningService {
    key_store: OnceLock<Arc<KeyStore>>,
}

#[tonic::async_trait]
impl OrchestratorKeyProvisioning for KeyProvisioningService {
    async fn send_group_keys(
        &self,
        _request: Request<SendGroupKeysRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        // TODO(#4442): Implement replacing group encryption key.
        Err(tonic::Status::unimplemented(
            "Key Provisioning is not implemented",
        ))
    }
}

struct KeyProvisioningLeaderService {
    key_store: Arc<KeyStore>,
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningLeaderService {
    async fn get_group_keys(
        &self,
        _request: Request<GetGroupKeysRequest>,
    ) -> Result<Response<GetGroupKeysResponse>, tonic::Status> {
        // TODO(#4442): Implement generating group encryption key.
        Err(tonic::Status::unimplemented(
            "Key Provisioning is not implemented",
        ))
    }
}
