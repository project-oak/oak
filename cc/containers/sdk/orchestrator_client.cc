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

#include "cc/containers/sdk/orchestrator_client.h"

#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/common.h"
#include "grpcpp/client_context.h"
#include "grpcpp/support/status.h"
#include "proto/containers/interfaces.pb.h"

namespace oak::containers::sdk {

namespace {
using ::oak::containers::GetApplicationConfigResponse;
}  // namespace

absl::StatusOr<std::string> OrchestratorClient::GetApplicationConfig() const {
  grpc::ClientContext context;
  context.set_authority(kContextAuthority);
  GetApplicationConfigResponse response;
  if (auto status = stub_->GetApplicationConfig(&context, {}, &response);
      !status.ok()) {
    return absl::Status(static_cast<absl::StatusCode>(status.error_code()),
                        status.error_message());
  }
  return std::move(*response.mutable_config());
}

absl::Status OrchestratorClient::NotifyAppReady() const {
  grpc::ClientContext context;
  context.set_authority(kContextAuthority);
  google::protobuf::Empty response;
  if (auto status = stub_->NotifyAppReady(&context, {}, &response);
      !status.ok()) {
    return absl::Status(static_cast<absl::StatusCode>(status.error_code()),
                        status.error_message());
  }
  return absl::OkStatus();
}

}  // namespace oak::containers::sdk
