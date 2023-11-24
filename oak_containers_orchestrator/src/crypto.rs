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

use crate::proto::oak::containers::v1::{
    orchestrator_crypto_server::OrchestratorCrypto, GetSessionKeysRequest, GetSessionKeysResponse,
    GetSignatureRequest, GetSignatureResponse, KeyOrigin,
};
use oak_crypto::encryptor::{EncryptionKeyProvider, RecipientContextGenerator};
use std::sync::Arc;
use tonic::{Request, Response};

pub(crate) struct KeyStore {
    instance_encryption_key: EncryptionKeyProvider,
    group_encryption_key: EncryptionKeyProvider,
}

impl KeyStore {
    pub(crate) fn new() -> Self {
        let instance_encryption_key = EncryptionKeyProvider::generate();
        let group_encryption_key = instance_encryption_key.clone();
        Self {
            instance_encryption_key,
            group_encryption_key,
        }
    }

    pub(crate) fn mutable_group_encryption_key<'a>(&'a mut self) -> &'a mut EncryptionKeyProvider {
        &mut self.group_encryption_key
    }
}

// TODO(#4442): Create CryptoService after group key was provisioned.
struct CryptoService {
    key_store: Arc<KeyStore>,
}

#[tonic::async_trait]
impl OrchestratorCrypto for CryptoService {
    async fn get_session_keys(
        &self,
        request: Request<GetSessionKeysRequest>,
    ) -> Result<Response<GetSessionKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        let encryption_key = match request.key_origin() {
            KeyOrigin::Instance => &self.key_store.instance_encryption_key,
            KeyOrigin::Group => &self.key_store.group_encryption_key,
        };

        let context = encryption_key
            .generate_recipient_context(&request.serialized_encapsulated_public_key)
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't generate crypto context: {err}"))
            })?
            .serialize()
            .map_err(|err| {
                tonic::Status::internal(format!("couldn't serialize crypto context: {err}"))
            })?;
        Ok(tonic::Response::new(GetSessionKeysResponse {
            context: Some(context),
        }))
    }

    async fn get_signature(
        &self,
        _request: Request<GetSignatureRequest>,
    ) -> Result<Response<GetSignatureResponse>, tonic::Status> {
        // TODO(#4504): Implement data signing.
        Err(tonic::Status::unimplemented("Signing is not implemented"))
    }
}
