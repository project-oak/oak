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

#include "asylo/grpc/auth/enclave_channel_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/identity/init.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"
#include "include/grpcpp/grpcpp.h"

#include "oak/proto/node.grpc.pb.h"
#include "oak/proto/scheduler.grpc.pb.h"

#include <fstream>

DEFINE_string(scheduler_address, "127.0.0.1:8888", "Address of the Oak Scheduler to connect to");
DEFINE_string(module, "", "File containing the compiled WebAssembly module");

// TODO: Move to a separate file.
class OakSchedulingClient {
 public:
  OakSchedulingClient(const std::shared_ptr<::grpc::ChannelInterface>& channel)
      : stub_(::oak::Scheduler::NewStub(channel, ::grpc::StubOptions())) {}

  oak::CreateNodeResponse CreateNode() {
    ::grpc::ClientContext context;

    ::oak::CreateNodeRequest request;
    ::oak::CreateNodeResponse response;

    std::ifstream t(FLAGS_module, std::ifstream::in);
    if (!t.is_open()) {
      LOG(QFATAL) << "Could not open file " << FLAGS_module;
    }
    std::stringstream buffer;
    buffer << t.rdbuf();
    LOG(INFO) << "Module size: " << buffer.str().size();

    request.set_module(buffer.str());

    LOG(INFO) << "Creating Oak Node";
    ::grpc::Status status = stub_->CreateNode(&context, request, &response);
    if (!status.ok()) {
      LOG(QFATAL) << "Failed: " << status.error_message();
    }

    LOG(INFO) << "Oak Node created: " << response.DebugString();
    return response;
  }

 private:
  std::unique_ptr<::oak::Scheduler::Stub> stub_;
};

int main(int argc, char** argv) {
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  if (FLAGS_scheduler_address.empty()) {
    LOG(QFATAL) << "Must supply a non-empty address with --scheduler_address";
  }

  if (FLAGS_module.empty()) {
    LOG(QFATAL) << "Must supply a non-empty module file with --module";
  }

  {
    LOG(INFO) << "Initializing assertion authorities";
    std::vector<::asylo::EnclaveAssertionAuthorityConfig> configs;
    ::asylo::Status status =
        ::asylo::InitializeEnclaveAssertionAuthorities(configs.begin(), configs.end());
    if (!status.ok()) {
      LOG(QFATAL) << "Could not initialize assertion authorities";
    }
    LOG(INFO) << "Assertion authorities initialized";
  }

  OakSchedulingClient scheduling_client(
      ::grpc::CreateChannel(FLAGS_scheduler_address, ::grpc::InsecureChannelCredentials()));
  oak::CreateNodeResponse create_node_response = scheduling_client.CreateNode();

  std::stringstream addr;
  addr << "127.0.0.1:" << create_node_response.port();
  LOG(INFO) << "Connecting to Oak Node: " << addr.str();
  std::unique_ptr<oak::Node::Stub> node = oak::Node::NewStub(::grpc::CreateChannel(
      addr.str(),
      ::asylo::EnclaveChannelCredentials(::asylo::BidirectionalNullCredentialsOptions())));
  LOG(INFO) << "Connected to Oak Node";

  {
    ::grpc::ClientContext context;

    ::oak::InvokeRequest request;
    ::oak::InvokeResponse response;

    request.set_data("WORLD");

    node->Invoke(&context, request, &response);
  }
}
