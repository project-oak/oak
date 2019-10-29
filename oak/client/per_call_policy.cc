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

#include "oak/client/per_call_policy.h"

#include <map>

#include "oak/common/nonce_generator.h"
#include "oak/common/policy.h"

namespace oak {

PerCallPolicy::PerCallPolicy() {}

grpc::Status PerCallPolicy::GetMetadata(grpc::string_ref service_url, grpc::string_ref method_name,
                                        const grpc::AuthContext& channel_auth_context,
                                        std::multimap<grpc::string, grpc::string>* metadata) {
  auto nonce = nonce_generator_.NextNonce();
  metadata->insert(
      std::make_pair(kOakAuthorizationBearerTokenGrpcMetadataKey, NonceToBase64(nonce)));
  // TODO: Also attach a policy restricting information flow to the freshly generated nonce, in
  // order to emulate a "pure computation" policy.
  return grpc::Status::OK;
}

}  // namespace oak
