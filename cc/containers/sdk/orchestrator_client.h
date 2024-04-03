/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_CONTAINERS_SDK_ORCHESTRATOR_CLIENT_H_
#define CC_CONTAINERS_SDK_ORCHESTRATOR_CLIENT_H_

#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/containers/sdk/common.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "oak_containers/proto/interfaces.grpc.pb.h"
#include "oak_containers/proto/interfaces.pb.h"

namespace oak::containers::sdk {

class OrchestratorClient {
 public:
  OrchestratorClient()
      : OrchestratorClient(grpc::CreateChannel(
            kOrchestratorSocket, grpc::InsecureChannelCredentials())) {}

  absl::StatusOr<std::string> GetApplicationConfig() const;
  absl::Status NotifyAppReady() const;

 private:
  explicit OrchestratorClient(const std::shared_ptr<grpc::Channel>& channel)
      : stub_(::oak::containers::Orchestrator::NewStub(channel)) {}

  std::unique_ptr<::oak::containers::Orchestrator::Stub> stub_;
};

}  // namespace oak::containers::sdk

#endif  // CC_CONTAINERS_SDK_ORCHESTRATOR_CLIENT_H_
