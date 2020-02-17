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

#include "oak/server/dev/dev_oak_loader.h"
#include "absl/memory/memory.h"
#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/init.h"
#include "asylo/util/logging.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {

DevOakLoader::DevOakLoader() { InitializeAssertionAuthorities(); }

grpc::Status DevOakLoader::CreateApplication(
    const oak::ApplicationConfiguration& application_configuration) {
  LOG(INFO) << "Creating an Oak application";

  auto runtime = absl::make_unique<OakRuntime>();
  auto status = runtime->Initialize(application_configuration);
  if (!status.ok()) {
    return status;
  }

  // Start the runtime.
  auto result = runtime->Start();
  runtime_ = std::move(runtime);
  return result;
}

grpc::Status DevOakLoader::TerminateApplication() {
  if (runtime_ == nullptr) {
    std::string error = "Terminating a non-existent application";
    LOG(ERROR) << error;
    return grpc::Status(grpc::StatusCode::INTERNAL, error);
  }
  LOG(INFO) << "Terminating an Oak application";

  runtime_->Stop();
  return grpc::Status::OK;
}

// Even if we are not running in an enclave, we are still relying on Asylo assertion authorities.
// This allows us to use the same client code to connect to the runtime, and it will potentially
// allow us to use non-enclave identities in the future.
void DevOakLoader::InitializeAssertionAuthorities() {
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

}  // namespace oak
