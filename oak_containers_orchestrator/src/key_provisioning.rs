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
    proto::oak::key_provisioning::v1::{
        key_provisioning_server::KeyProvisioning, GetGroupKeysRequest, GetGroupKeysResponse,
    },
};
use std::sync::{Arc, OnceLock};
use tonic::{Request, Response};

#[allow(dead_code)]
/// Dependant is a Key Provisioning role that requests group keys from the
/// Key Provisioning Leader.
struct KeyProvisioningDependant {
    _key_store: OnceLock<Arc<KeyStore>>,
}

struct KeyProvisioningService {
    _key_store: Arc<KeyStore>,
}

#[tonic::async_trait]
impl KeyProvisioning for KeyProvisioningService {
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
