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
  ManagerClient(const std::shared_ptr<::grpc::ChannelInterface>& channel)
      : stub_(::oak::Manager::NewStub(channel, ::grpc::StubOptions())) {}

  // TODO: Return StatusOr<::oak::CreateNodeResponse>.
  ::oak::CreateNodeResponse CreateNode(const std::string& module_bytes) {
    ::grpc::ClientContext context;

    ::oak::CreateNodeRequest request;
    ::oak::CreateNodeResponse response;

    request.set_module(module_bytes);

    LOG(INFO) << "Creating Oak Node";
    ::grpc::Status status = stub_->CreateNode(&context, request, &response);
    if (!status.ok()) {
      LOG(QFATAL) << "Failed: " << status.error_code() << '/'
		  << status.error_message() << '/' << status.error_details();
    }

    LOG(INFO) << "Oak Node created: " << response.DebugString();
    return response;
  }

 private:
  std::unique_ptr<::oak::Manager::Stub> stub_;
};

}  // namespace oak
