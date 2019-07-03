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

  // TODO: Return StatusOr<::oak::CreateApplicationResponse>.
  CreateApplicationResponse CreateApplication(const std::string& module_bytes) {
    grpc::ClientContext context;

    CreateApplicationRequest request;
    CreateApplicationResponse response;

    // Build an application configuration with a single WebAssembly node with the provided
    // WebAssembly module bytes and no channels.
    // TODO: Replace with explicit gRPC and Log pseudo-Nodes (and associated channels) when
    // available.
    ApplicationConfiguration* application_configuration =
        request.mutable_application_configuration();
    Node* node = application_configuration->add_nodes();
    WebAssemblyNode* web_assembly_node = node->mutable_web_assembly_node();
    web_assembly_node->set_module_bytes(module_bytes);

    LOG(INFO) << "Creating Oak Node";
    grpc::Status status = stub_->CreateApplication(&context, request, &response);
    if (!status.ok()) {
      LOG(QFATAL) << "Failed: " << status.error_code() << '/' << status.error_message() << '/'
                  << status.error_details();
    }

    LOG(INFO) << "Oak Node created: " << response.DebugString();
    return response;
  }

 private:
  std::unique_ptr<Manager::Stub> stub_;
};

}  // namespace oak
