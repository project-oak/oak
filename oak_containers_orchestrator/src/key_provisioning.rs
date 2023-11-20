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

use crate::proto::oak::containers::{
    orchestrator_key_provisioning_server::OrchestratorKeyProvisioning, SendProvisionSecretsRequest,
};
use oak_key_provisioning::proto::oak::oak_key_provisioning::{
    key_provisioning_server::KeyProvisioning,
    GetProvisionSecretsRequest, GetProvisionSecretsResponse,
};
use tonic::{Request, Response};

struct KeyProvisioningService {}

#[tonic::async_trait]
impl OrchestratorKeyProvisioning for KeyProvisioningService {
    async fn send_provision_secrets(
        &self,
        _request: Request<SendProvisionSecretsRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        Ok(tonic::Response::new(()))
    }
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningService {
    async fn get_provision_secrets(
        &self,
        _request: Request<GetProvisionSecretsRequest>,
    ) -> Result<Response<GetProvisionSecretsResponse>, tonic::Status> {
        Ok(tonic::Response::new(GetProvisionSecretsResponse {
            encrypted_encryption_key: None,
        }))
    }
}
