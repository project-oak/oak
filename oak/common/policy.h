/*
 * Copyright 2019 The Project Oak Authors
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

#ifndef OAK_COMMON_POLICY_H_
#define OAK_COMMON_POLICY_H_

#include "absl/base/attributes.h"
#include "oak/proto/label.pb.h"

namespace oak {

// Metadata key used to refer to the Oak Policy associated with the gRPC request. This is
// effectively treated as the name of a custom HTTP header.
ABSL_CONST_INIT extern const char kOakPolicyGrpcMetadataKey[];

// Metadata key used to refer to per-call authorization tokens.
//
// Each call may have multiple tokens under the same metadata key, in which case their authorities
// get combined.
//
// Tokens are similar to OAuth2.0 access tokens, in that they grant the client the ability to access
// data protected by the corresponding policies, for each token provided.
//
// See https://tools.ietf.org/html/rfc6750
ABSL_CONST_INIT extern const char kOakAuthorizationBearerTokenGrpcMetadataKey[];

// Serialized the provided policy so that it can be sent as a binary gRPC metadata value.
std::string SerializePolicy(const oak::label::Label& policy_proto);

// Deserializes the provided binary gRPC metadata value into a policy.
oak::label::Label DeserializePolicy(const std::string& policy_bytes);

// Creates a policy that only allows declassifying data for gRPC clients that can present the
// provided authorization bearer token.
oak::label::Label AuthorizationBearerTokenPolicy(const std::string& authorization_token_hmac);

// Creates a policy that only allows declassifying data for modules that match the
// provided module attestation.
oak::label::Label WebAssemblyModuleAttestationPolicy(const std::string& module_attestation);

}  // namespace oak

#endif  // OAK_COMMON_POLICY_H_
