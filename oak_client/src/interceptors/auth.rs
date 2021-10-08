//
// Copyright 2020 The Project Oak Authors
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

use log::error;
use oak_abi::proto::oak::identity::SignedChallenge;
use oak_sign::KeyPair;
use prost::Message;
use tonic::{metadata::MetadataValue, service::interceptor::Interceptor, Code, Request, Status};

/// Intercepts gRPC requests and authenticates the client with the provided [`KeyPair`].
#[derive(Clone)]
pub struct AuthInterceptor {
    /// Key pair to use for authentication.
    key_pair: KeyPair,
}

impl AuthInterceptor {
    pub fn create(key_pair: KeyPair) -> Self {
        Self { key_pair }
    }
}

impl Interceptor for AuthInterceptor {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        let mut request = request;

        let signature =
            oak_sign::SignatureBundle::create(oak_abi::OAK_CHALLENGE.as_bytes(), &self.key_pair)
                .map_err(|err| Status::new(Code::InvalidArgument, format!("{:?}", err)))?;

        // Signed challenge
        let signed_challenge = SignedChallenge {
            signed_hash: signature.signed_hash,
            public_key: self.key_pair.public_key_der().map_err(|err| {
                error!("could not parse public key: {:?}", err);
                tonic::Status::internal("could not parse public key")
            })?,
        };

        let mut signed_challenge_bytes = Vec::new();
        signed_challenge
            .encode(&mut signed_challenge_bytes)
            .map_err(|err| {
                error!("could not encode signed challenge to protobuf: {:?}", err);
                tonic::Status::internal("could not encode signed challenge to protobuf")
            })?;
        request.metadata_mut().insert_bin(
            oak_abi::OAK_SIGNED_CHALLENGE_GRPC_METADATA_KEY,
            MetadataValue::from_bytes(&signed_challenge_bytes),
        );
        Ok(request)
    }
}
