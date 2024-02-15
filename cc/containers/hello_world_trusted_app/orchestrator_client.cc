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
#include "cc/containers/hello_world_trusted_app/orchestrator_client.h"

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "google/protobuf/empty.pb.h"
#include "grpcpp/channel.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "oak_containers/proto/interfaces.grpc.pb.h"
#include "oak_containers/proto/interfaces.pb.h"
#include "proto/containers/orchestrator_crypto.grpc.pb.h"
#include "proto/containers/orchestrator_crypto.pb.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

using ::oak::containers::GetApplicationConfigResponse;
using ::oak::containers::v1::DeriveSessionKeysRequest;
using ::oak::containers::v1::DeriveSessionKeysResponse;
using ::oak::crypto::RecipientContext;

OrchestratorClient::OrchestratorClient()
    : OrchestratorClient(grpc::CreateChannel("unix:/oak_utils/orchestrator_ipc",
                                             grpc::InsecureChannelCredentials())) {}

OrchestratorClient::OrchestratorClient(const std::shared_ptr<grpc::Channel>& channel)
    : stub_(containers::Orchestrator::NewStub(channel)),
      crypto_stub_(containers::v1::OrchestratorCrypto::NewStub(channel)) {}

absl::StatusOr<std::string> OrchestratorClient::GetApplicationConfig() const {
  grpc::ClientContext context;
  GetApplicationConfigResponse response;
  if (auto status = stub_->GetApplicationConfig(&context, {}, &response); !status.ok()) {
    return absl::Status(static_cast<absl::StatusCode>(status.error_code()), status.error_message());
  }
  return std::move(*response.mutable_config());
}

absl::Status OrchestratorClient::NotifyAppReady() const {
  grpc::ClientContext context;
  google::protobuf::Empty response;
  if (auto status = stub_->NotifyAppReady(&context, {}, &response); !status.ok()) {
    return absl::Status(static_cast<absl::StatusCode>(status.error_code()), status.error_message());
  }
  return absl::OkStatus();
}

absl::StatusOr<std::unique_ptr<RecipientContext>> OrchestratorClient::GenerateRecipientContext(
    absl::string_view serialized_encapsulated_public_key) {
  grpc::ClientContext context;
  DeriveSessionKeysRequest request;
  request.set_key_origin(containers::v1::KeyOrigin::INSTANCE);
  request.set_serialized_encapsulated_public_key(serialized_encapsulated_public_key);
  DeriveSessionKeysResponse response;
  if (auto status = crypto_stub_->DeriveSessionKeys(&context, request, &response); !status.ok()) {
    return absl::Status(static_cast<absl::StatusCode>(status.error_code()), status.error_message());
  }
  return RecipientContext::Deserialize(response.session_keys());
}

}  // namespace oak::oak_containers_hello_world_trusted_app
