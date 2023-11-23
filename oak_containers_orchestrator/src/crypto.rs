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
use tonic::{Request, Response};

// TODO(#4442): Create CryptoService after group key was provisioned.
struct CryptoService {
    instance_encryption_key: EncryptionKeyProvider,
    group_encryption_key: EncryptionKeyProvider,
}

#[tonic::async_trait]
impl OrchestratorCrypto for CryptoService {
    async fn get_session_keys(
        &self,
        request: Request<GetSessionKeysRequest>,
    ) -> Result<Response<GetSessionKeysResponse>, tonic::Status> {
        let request = request.into_inner();

        let encryption_key = match request.key_origin() {
            KeyOrigin::Instance => &self.instance_encryption_key,
            KeyOrigin::Group => &self.group_encryption_key,
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
