/*
 * Copyright 2024 The Project Oak Authors
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

#ifndef CC_CONTAINERS_SDK_ORCHESTRATOR_CRYPTO_CLIENT_H_
#define CC_CONTAINERS_SDK_ORCHESTRATOR_CRYPTO_CLIENT_H_

#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/common.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "proto/containers/orchestrator_crypto.grpc.pb.h"
#include "proto/containers/orchestrator_crypto.pb.h"

namespace oak::containers::sdk {

class OrchestratorCryptoClient {
 public:
  OrchestratorCryptoClient()
      : OrchestratorCryptoClient(grpc::CreateChannel(
            kOrchestratorSocket, grpc::InsecureChannelCredentials())) {}

  absl::StatusOr<::oak::crypto::v1::SessionKeys> DeriveSessionKeys(
      ::oak::containers::v1::KeyOrigin key_origin,
      absl::string_view serialized_encapsulated_public_key) const;

  absl::StatusOr<::oak::crypto::v1::Signature> Sign(
      ::oak::containers::v1::KeyOrigin key_origin,
      absl::string_view message) const;

 private:
  explicit OrchestratorCryptoClient(
      const std::shared_ptr<grpc::Channel>& channel)
      : stub_(::oak::containers::v1::OrchestratorCrypto::NewStub(channel)) {}

  std::unique_ptr<::oak::containers::v1::OrchestratorCrypto::Stub> stub_;
};

}  // namespace oak::containers::sdk

#endif  // CC_CONTAINERS_SDK_ORCHESTRATOR_CRYPTO_CLIENT_H_
