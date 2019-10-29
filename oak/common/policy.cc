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

#include "oak/common/policy.h"

#include "absl/strings/escaping.h"

namespace oak {

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
const char kOakPolicyGrpcMetadataKey[] = "x-oak-policy-bin";

// The `-bin` suffix allows sending binary data for this metadata key.
//
// See https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md.
const char kOakAuthorizationBearerTokenGrpcMetadataKey[] = "x-oak-authorization-bearer-token-bin";

std::string SerializePolicy(const oak::policy::Labels& policy_proto) {
  return policy_proto.SerializeAsString();
}

oak::policy::Labels DeserializePolicy(const std::string& policy_bytes) {
  oak::policy::Labels policy_proto;
  // TODO: Check errors.
  policy_proto.ParseFromString(policy_bytes);
  return policy_proto;
}

oak::policy::Labels AuthorizationBearerTokenPolicy(const std::string& authorization_token) {
  oak::policy::Labels labels;
  auto secrecy_tags = labels.add_secrecy_tags();
  auto grpc_tag = secrecy_tags->mutable_grpc_tag();
  grpc_tag->set_authorization_bearer_token(authorization_token);
  return labels;
}

}  // namespace oak
