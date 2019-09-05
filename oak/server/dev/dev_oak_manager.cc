/*
 * Copyright 2018 The Project Oak Authors
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

#include "dev_oak_manager.h"

#include "absl/memory/memory.h"
#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/init.h"
#include "asylo/util/logging.h"
#include "grpcpp/support/status_code_enum.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {

DevOakManager::DevOakManager() : Service(), next_application_id_(0) {
  LOG(INFO) << "Creating OakManager";
  InitializeAssertionAuthorities();
}

grpc::Status DevOakManager::CreateApplication(grpc::ServerContext* context,
                                              const oak::CreateApplicationRequest* request,
                                              oak::CreateApplicationResponse* response) {
  std::string application_id = NewApplicationId();
  LOG(INFO) << "Creating app with with id: " << application_id;

  auto runtime = absl::make_unique<OakRuntime>();
  auto status = runtime->Initialize(request->application_configuration());
  if (!status.ok()) {
    return status.ToOtherStatus<grpc::Status>();
  }

  // Start the runtime.
  runtime->Start();

  int32_t port = runtime->GetPort();
  LOG(INFO) << "gRPC server is listening on port: " << port;

  response->set_application_id(application_id);
  response->set_grpc_port(port);

  runtimes_[application_id] = std::move(runtime);
  return grpc::Status::OK;
}

// Even if we are not running in an enclave, we are still relying on Asylo assertion authorities
// This allows us to use the same client code to connect to the runtime, and it will potentially
// allow us to use non-enclave identities in the future.
void DevOakManager::InitializeAssertionAuthorities() {
  LOG(INFO) << "Initializing assertion authorities";
  asylo::EnclaveAssertionAuthorityConfig null_config;
  asylo::SetNullAssertionDescription(null_config.mutable_description());
  std::vector<asylo::EnclaveAssertionAuthorityConfig> configs = {
      null_config,
  };
  asylo::Status status =
      asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
  if (!status.ok()) {
    LOG(QFATAL) << "Could not initialize assertion authorities";
  }
  LOG(INFO) << "Assertion authorities initialized";
}

std::string DevOakManager::NewApplicationId() {
  // For dev purposes, just increment a value
  std::stringstream id_str;
  id_str << next_application_id_;
  next_application_id_ += 1;
  return id_str.str();
}

}  // namespace oak
