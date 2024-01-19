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
#include "absl/strings/string_view.h"
#include "cc/containers/hello_world_trusted_app/orchestrator_client.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers_hello_world_trusted_app/proto/interface.grpc.pb.h"
#include "oak_containers_hello_world_trusted_app/proto/interface.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

class TrustedApplicationImpl : public containers::example::TrustedApplication::Service {
 public:
  TrustedApplicationImpl(OrchestratorClient* orchestrator_client,
                         absl::string_view application_config)
      : orchestrator_client_(*ABSL_DIE_IF_NULL(orchestrator_client)),
        application_config_(application_config) {}

  grpc::Status Hello(grpc::ServerContext* context, const containers::example::HelloRequest* request,
                     containers::example::HelloResponse* response) override;

 private:
  OrchestratorClient& orchestrator_client_;
  const std::string application_config_;
};

}  // namespace oak::oak_containers_hello_world_trusted_app

#endif  // CC_OAK_CONTAINERS_HELLO_WORLD_TRUSTED_APP_APP_SERVICE_H_
