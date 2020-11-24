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

use super::Interceptor;
use log::error;
use oak_abi::proto::oak::identity::SignedChallenge;
use oak_sign::KeyPair;
use prost::Message;
use tonic::{metadata::MetadataValue, Request, Status};

/// Intercepts gRPC requests and authenticates the client with the provided [`KeyPair`].
pub struct AuthInterceptor {
    /// Key pair to use for authentication.
    ///
    /// Ideally this would just be a reference instead of an actual value, but
    /// [`tonic::Interceptor::new`] requires a `'static` lifetime, so it would need to be cloned
    /// anyway in order to be used.
    key_pair: KeyPair,
}

impl AuthInterceptor {
    pub fn create(key_pair: KeyPair) -> Self {
        Self { key_pair }
    }
}

impl Interceptor for AuthInterceptor {
    fn process(&self, request: Request<()>) -> Result<Request<()>, Status> {
        let mut request = request;
        let signed_challenge = SignedChallenge {
            signed_hash: self.key_pair.sign(oak_abi::OAK_CHALLENGE.as_bytes()),
            public_key: self.key_pair.pkcs8_public_key(),
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

impl Into<tonic::Interceptor> for AuthInterceptor {
    fn into(self) -> tonic::Interceptor {
        tonic::Interceptor::new(move |request: Request<()>| self.process(request))
    }
}
