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

#ifndef OAK_CLIENT_SIGNATURE_METADATA_H_
#define OAK_CLIENT_SIGNATURE_METADATA_H_

#include "absl/base/attributes.h"
#include "include/grpcpp/grpcpp.h"
#include "oak_abi/proto/identity.pb.h"

namespace oak {

// Metadata key used to refer to the signed challenge associated with the gRPC request. This is
// effectively treated as the name of a custom HTTP header.
ABSL_CONST_INIT extern const char kOakSignedChallengeGrpcMetadataKey[];

// The fixed challenge for challenge-response-based authentication.
// TODO(#1357): Remove, or move to tests, when we have a per-connection challenge string.
ABSL_CONST_INIT extern const char kOakChallenge[];

// This class injects the provided signed challenge to each outgoing gRPC call, passed over gRPC
// binary metadata.
//
// See https://grpc.io/docs/guides/auth/.
class SignatureMetadata : public grpc::MetadataCredentialsPlugin {
 public:
  SignatureMetadata(const oak::identity::SignedChallenge signed_challenge);

  grpc::Status GetMetadata(grpc::string_ref service_url, grpc::string_ref method_name,
                           const grpc::AuthContext& channel_auth_context,
                           std::multimap<grpc::string, grpc::string>* metadata) override;

 private:
  const std::string serialized_signed_challenge_;
};

}  // namespace oak

#endif  // OAK_CLIENT_SIGNATURE_METADATA_H_
