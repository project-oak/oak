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
#include "include/grpcpp/grpcpp.h"
#include "oak/common/logging.h"

namespace oak {

DevOakLoader::DevOakLoader() {}

grpc::Status DevOakLoader::CreateApplication(
    const oak::ApplicationConfiguration& application_configuration,
    std::shared_ptr<grpc::ServerCredentials> grpc_credentials) {
  OAK_LOG(INFO) << "Creating an Oak application";

  auto runtime = absl::make_unique<OakRuntime>();
  auto status = runtime->Initialize(application_configuration, grpc_credentials);
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
    OAK_LOG(ERROR) << error;
    return grpc::Status(grpc::StatusCode::INTERNAL, error);
  }
  OAK_LOG(INFO) << "Terminating an Oak application";

  runtime_->Stop();
  return grpc::Status::OK;
}

}  // namespace oak
