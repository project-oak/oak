/*
 * Copyright 2019 The Project Oak Authors
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

#include "absl/memory/memory.h"
#include "oak/common/app_config.h"
#include "oak/proto/manager.grpc.pb.h"

namespace oak {

// A client connected to an Oak Manager instance.
//
// It allows creating new Oak Node instances based on the Oak Module provided.
//
// TODO: Allow specifying policy configuration in the CreateNode request.
class ManagerClient {
 public:
  ManagerClient(const std::shared_ptr<grpc::ChannelInterface>& channel)
      : stub_(Manager::NewStub(channel, grpc::StubOptions())) {}

  // TODO: Return StatusOr<std::unique_ptr<CreateApplicationResponse>> instead of just nullptr.
  std::unique_ptr<CreateApplicationResponse> CreateApplication(const std::string& module_bytes) {
    return CreateApplication(module_bytes, true, "");
  }

  std::unique_ptr<CreateApplicationResponse> CreateApplication(const std::string& module_bytes,
                                                               bool enable_logging,
                                                               const std::string& storage_address) {
    grpc::ClientContext context;

    CreateApplicationRequest request;
    auto response = absl::make_unique<CreateApplicationResponse>();

    // Build an application configuration with a single WebAssembly node with the provided
    // WebAssembly module bytes.
    std::unique_ptr<ApplicationConfiguration> application_config =
        DefaultConfig("app", module_bytes);
    if (enable_logging) {
      AddLoggingToConfig(application_config.get());
    }
    if (!storage_address.empty()) {
      AddStorageToConfig(application_config.get(), "app", storage_address);
    }
    request.set_allocated_application_configuration(application_config.release());

    LOG(INFO) << "Creating Oak Application";
    grpc::Status status = stub_->CreateApplication(&context, request, response.get());
    if (!status.ok()) {
      LOG(ERROR) << "Failed: " << status.error_code() << '/' << status.error_message() << '/'
                 << status.error_details();
      return nullptr;
    }

    LOG(INFO) << "Oak Application created: " << response->DebugString();
    return response;
  }

  void TerminateApplication(const std::string& application_id) {
    grpc::ClientContext context;

    TerminateApplicationRequest request;
    TerminateApplicationResponse response;
    request.set_application_id(application_id);

    LOG(INFO) << "Terminating Oak Application";
    grpc::Status status = stub_->TerminateApplication(&context, request, &response);
    if (!status.ok()) {
      LOG(ERROR) << "Failed: " << status.error_code() << '/' << status.error_message() << '/'
                 << status.error_details();
    }

    LOG(INFO) << "Termination response: " << response.DebugString();
  }

 private:
  std::unique_ptr<Manager::Stub> stub_;
};

}  // namespace oak
