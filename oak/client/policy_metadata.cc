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

namespace oak {

const absl::string_view kOakPolicyMetadataKey = "x-oak-policy";

PolicyMetadata::PolicyMetadata() {}

grpc::Status PolicyMetadata::GetMetadata(grpc::string_ref service_url, grpc::string_ref method_name,
                                         const grpc::AuthContext& channel_auth_context,
                                         std::multimap<grpc::string, grpc::string>* metadata) {
  // TODO: Make actual policy configurable. For now we are injecting a nonsense policy, which the
  // server is not even checking yet.
  metadata->insert(std::make_pair(kOakPolicyMetadataKey, "test-oak-policy"));
  return grpc::Status::OK;
}

}  // namespace oak
