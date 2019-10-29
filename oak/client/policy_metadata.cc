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

#include "oak/client/policy_metadata.h"

#include <map>
#include <utility>

#include "absl/strings/escaping.h"
#include "oak/common/policy.h"

namespace oak {

PolicyMetadata::PolicyMetadata(const oak::policy::Labels& labels)
    : serialized_policy_(SerializePolicy(labels)) {}

grpc::Status PolicyMetadata::GetMetadata(grpc::string_ref service_url, grpc::string_ref method_name,
                                         const grpc::AuthContext& channel_auth_context,
                                         std::multimap<grpc::string, grpc::string>* metadata) {
  metadata->insert(std::make_pair(kOakPolicyGrpcMetadataKey, serialized_policy_));
  return grpc::Status::OK;
}

}  // namespace oak
