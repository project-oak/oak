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

#ifndef OAK_COMMON_LABEL_H_
#define OAK_COMMON_LABEL_H_

#include "absl/base/attributes.h"
#include "oak/proto/label.pb.h"

namespace oak {

// Metadata key used to refer to the Oak Label associated with the gRPC request. This is
// effectively treated as the name of a custom HTTP header.
ABSL_CONST_INIT extern const char kOakLabelGrpcMetadataKey[];

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

// Serialized the provided label so that it can be sent as a binary gRPC metadata value.
std::string SerializeLabel(const oak::label::Label& label_proto);

// Deserializes the provided binary gRPC metadata value into a label.
oak::label::Label DeserializeLabel(const std::string& label_bytes);

// Creates a label that only allows declassifying data for gRPC clients that can present the
// provided authorization bearer token.
oak::label::Label AuthorizationBearerTokenLabel(const std::string& authorization_token_hmac);

// Creates a label that only allows declassifying data for modules that match the provided module
// attestation.
oak::label::Label WebAssemblyModuleAttestationLabel(const std::string& module_attestation);

// Creates a public untrusted label, which is the least confidential and least trusted label and
// applies no confidentiality restrictions to the data contained in the request.
oak::label::Label PublicUntrustedLabel();

}  // namespace oak

#endif  // OAK_COMMON_LABEL_H_
