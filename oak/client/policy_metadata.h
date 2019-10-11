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

#ifndef OAK_CLIENT_POLICY_METADATA_H_
#define OAK_CLIENT_POLICY_METADATA_H_

#include "absl/base/attributes.h"
#include "absl/strings/string_view.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {

// Metadata key used to refer to Oak Policies associated with the gRPC request. This is effectively
// treated as the name of a custom HTTP header.
ABSL_CONST_INIT extern const absl::string_view kOakPolicyMetadataKey;

// This class injects a pre-determined Oak Policy to each outgoing gRPC call.
// In real-world use cases it should be combined to channel credentials, providing enclave
// attestation.
// See https://grpc.io/docs/guides/auth/.
class PolicyMetadata : public grpc::MetadataCredentialsPlugin {
 public:
  PolicyMetadata();

  grpc::Status GetMetadata(grpc::string_ref service_url, grpc::string_ref method_name,
                           const grpc::AuthContext& channel_auth_context,
                           std::multimap<grpc::string, grpc::string>* metadata) override;
};

}  // namespace oak

#endif  // OAK_CLIENT_POLICY_METADATA_H_
