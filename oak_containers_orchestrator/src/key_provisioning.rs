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

use std::sync::Arc;

use oak_attestation_verification::verifier::verify_dice_chain;
use tonic::{Request, Response};

use crate::{
    crypto::KeyStore,
    proto::oak::key_provisioning::v1::{
        key_provisioning_server::KeyProvisioning, GetGroupKeysRequest, GetGroupKeysResponse,
        GroupKeys,
    },
};

struct KeyProvisioningService {
    key_store: Arc<KeyStore>,
}

impl KeyProvisioningService {
    pub fn new(key_store: Arc<KeyStore>) -> Self {
        Self { key_store }
    }
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningService {
    async fn get_group_keys(
        &self,
        request: Request<GetGroupKeysRequest>,
    ) -> Result<Response<GetGroupKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        // Verify attestation evidence and get encryption public key, which will be used to encrypt
        // group keys.
        let evidence = request.evidence.ok_or(tonic::Status::invalid_argument(
            "request message doesn't contain evidence",
        ))?;
        let _endorsements = request.endorsements.ok_or(tonic::Status::invalid_argument(
            "request message doesn't contain endorsements",
        ))?;
        // TODO(#4442): Provide reference values by the hostlib and use `verify` function.
        let attestation_results = verify_dice_chain(&evidence).map_err(|err| {
            tonic::Status::invalid_argument(format!("couldn't verify endorsed evidence: {err}"))
        })?;

        // Encrypt group keys.
        let encrypted_encryption_private_key = self
            .key_store
            .encrypted_group_encryption_key(&attestation_results.encryption_public_key)
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't encrypt encryption private key: {err}"))
            })?;
        let group_keys = GroupKeys {
            encrypted_encryption_private_key: Some(encrypted_encryption_private_key),
        };
        Ok(tonic::Response::new(GetGroupKeysResponse {
            group_keys: Some(group_keys),
        }))
    }
}
