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
#ifndef CC_OAK_CONTAINERS_SDK_ORCHESTRATOR_CLIENT_H_
#define CC_OAK_CONTAINERS_SDK_ORCHESTRATOR_CLIENT_H_

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/encryption_key.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "grpcpp/channel.h"
#include "oak_containers/proto/interfaces.grpc.pb.h"
#include "proto/containers/orchestrator_crypto.grpc.pb.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::containers::sdk {

class OrchestratorClient : public crypto::EncryptionKeyHandle {
 public:
  OrchestratorClient();

  absl::StatusOr<std::string> GetApplicationConfig() const;

  absl::Status NotifyAppReady() const;

  absl::StatusOr<std::unique_ptr<crypto::RecipientContext>> GenerateRecipientContext(
      absl::string_view serialized_encapsulated_public_key) override;

 private:
  explicit OrchestratorClient(const std::shared_ptr<grpc::Channel>& channel);

  std::unique_ptr<containers::Orchestrator::Stub> stub_;
  std::unique_ptr<containers::v1::OrchestratorCrypto::Stub> crypto_stub_;
};

}  // namespace oak::oak_containers_hello_world_trusted_app

#endif  // CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_ORCHESTRATOR_CLIENT_H_
