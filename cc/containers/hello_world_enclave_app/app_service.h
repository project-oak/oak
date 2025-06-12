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
#ifndef CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_
#define CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_

#include <string>

#include "absl/log/die_if_null.h"
#include "absl/log/log.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/encryption_key_handle.h"
#include "cc/containers/sdk/oak_session.h"
#include "cc/containers/sdk/orchestrator_client.h"
#include "cc/oak_session/server_session.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers/examples/hello_world/proto/hello_world.grpc.pb.h"
#include "oak_containers/examples/hello_world/proto/hello_world.pb.h"

namespace oak::containers::hello_world_enclave_app {

class EnclaveApplicationImpl
    : public oak::containers::example::EnclaveApplication::Service {
 public:
  EnclaveApplicationImpl(
      oak::containers::sdk::OakSessionContext oak_session_context,
      absl::string_view application_config)
      : oak_session_context_(std::move(oak_session_context)),
        application_config_(application_config) {}

  grpc::Status LegacySession(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<oak::session::v1::ResponseWrapper,
                               oak::session::v1::RequestWrapper>* stream)
      override;

  grpc::Status OakSession(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<oak::session::v1::SessionResponse,
                               oak::session::v1::SessionRequest>* stream)
      override;

  grpc::Status PlaintextSession(
      grpc::ServerContext* context,
      grpc::ServerReaderWriter<oak::session::v1::PlaintextMessage,
                               oak::session::v1::PlaintextMessage>* stream)
      override;

 private:
  std::string HandleRequest(absl::string_view request);
  oak::containers::sdk::OakSessionContext oak_session_context_;
  const oak::session::v1::EndorsedEvidence endorsed_evidence_;
  const std::string application_config_;
};

}  // namespace oak::containers::hello_world_enclave_app

#endif  // CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_
