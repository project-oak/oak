/*
 * Copyright 2021 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "oak/client/signature_metadata.h"
namespace oak {

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
//
// Keep in sync with OAK_SIGNED_CHALLENGE_GRPC_METADATA_KEY in `oak_abi/src/lib.rs`.
const char kOakSignedChallengeGrpcMetadataKey[] = "x-oak-signed-auth-challenge-bin";

// Keep in sync with OAK_CHALLENGE in `oak_abi/src/lib.rs`.
const char kOakChallenge[] = "oak-challenge";

SignatureMetadata::SignatureMetadata(const oak::identity::SignedChallenge signed_challenge)
    : serialized_signed_challenge_(signed_challenge.SerializeAsString()) {}

grpc::Status SignatureMetadata::GetMetadata(grpc::string_ref /*service_url*/,
                                            grpc::string_ref /*method_name*/,
                                            const grpc::AuthContext& /*channel_auth_context*/,
                                            std::multimap<grpc::string, grpc::string>* metadata) {
  metadata->insert(
      std::make_pair(kOakSignedChallengeGrpcMetadataKey, serialized_signed_challenge_));
  return grpc::Status::OK;
}

}  // namespace oak
