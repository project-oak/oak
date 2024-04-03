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
#include <memory>

#include "absl/log/check.h"
#include "absl/log/initialize.h"
#include "absl/status/statusor.h"
#include "app_service.h"
#include "cc/containers/hello_world_trusted_app/app_service.h"
#include "cc/containers/sdk/encryption_key_handle.h"
#include "cc/containers/sdk/orchestrator_client.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"

using ::oak::containers::sdk::OrchestratorClient;
using ::oak::oak_containers_hello_world_trusted_app::TrustedApplicationImpl;

int main(int argc, char* argv[]) {
  absl::InitializeLog();

  OrchestratorClient client;
  absl::StatusOr<std::string> application_config =
      client.GetApplicationConfig();
  QCHECK_OK(application_config);
  TrustedApplicationImpl service(
      std::make_unique<::oak::containers::sdk::InstanceEncryptionKeyHandle>(),
      *application_config);

  grpc::ServerBuilder builder;
  builder.AddListeningPort("[::]:8080", grpc::InsecureServerCredentials());
  builder.RegisterService(&service);
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  QCHECK_OK(client.NotifyAppReady());
  server->Wait();
  return 0;
}
