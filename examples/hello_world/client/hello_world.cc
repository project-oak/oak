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

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"
#include "include/grpcpp/grpcpp.h"

#include "examples/utils/utils.h"
#include "oak/client/node_client.h"
#include "oak/client/scheduler_client.h"

DEFINE_string(scheduler_address, "127.0.0.1:8888", "Address of the Oak Scheduler to connect to");
DEFINE_string(module, "", "File containing the compiled WebAssembly module");

int main(int argc, char** argv) {
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  // Connect to the Oak Scheduler.
  std::unique_ptr<::oak::SchedulerClient> scheduler_client =
      ::absl::make_unique<::oak::SchedulerClient>(
          ::grpc::CreateChannel(FLAGS_scheduler_address, ::grpc::InsecureChannelCredentials()));

  // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string module_bytes = ::oak::utils::read_file(FLAGS_module);
  ::oak::CreateNodeResponse create_node_response = scheduler_client->CreateNode(module_bytes);

  std::stringstream addr;
  addr << "127.0.0.1:" << create_node_response.port();
  LOG(INFO) << "Connecting to Oak Node: " << addr.str();

  // Connect to the newly created Oak Node.
  std::unique_ptr<::oak::NodeClient> node_client = ::absl::make_unique<::oak::NodeClient>(
      ::grpc::CreateChannel(addr.str(), ::asylo::EnclaveChannelCredentials(
                                            ::asylo::BidirectionalNullCredentialsOptions())));

  // Perform multiple invocations of the same Oak Node, with different parameters.
  {
    std::string response = node_client->Invoke("WORLD");
    LOG(INFO) << "response: " << response;
  }
  {
    std::string response = node_client->Invoke("MONDO");
    LOG(INFO) << "response: " << response;
  }
  {
    std::string response = node_client->Invoke("世界");
    LOG(INFO) << "response: " << response;
  }

  return 0;
}
