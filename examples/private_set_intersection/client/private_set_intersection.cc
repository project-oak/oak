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

#include "examples/private_set_intersection/proto/private_set_intersection.grpc.pb.h"
#include "examples/private_set_intersection/proto/private_set_intersection.pb.h"
#include "examples/utils/utils.h"
#include "oak/client/manager_client.h"
#include "oak/client/node_client.h"

DEFINE_string(manager_address, "127.0.0.1:8888", "Address of the Oak Manager to connect to");
DEFINE_string(module, "", "File containing the compiled WebAssembly module");

using ::oak::examples::private_set_intersection::GetIntersectionResponse;
using ::oak::examples::private_set_intersection::PrivateSetIntersection;
using ::oak::examples::private_set_intersection::SubmitSetRequest;

void SubmitSet(PrivateSetIntersection::Stub* stub, std::vector<std::string> set) {
  ::grpc::ClientContext context;
  SubmitSetRequest request;
  for (auto item : set) {
    request.add_values(item);
  }
  ::google::protobuf::Empty response;
  ::grpc::Status status = stub->SubmitSet(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not submit set: " << status.error_code() << ": "
                << status.error_message();
  }
}

std::vector<std::string> RetrieveIntersection(PrivateSetIntersection::Stub* stub) {
  std::vector<std::string> values;
  ::grpc::ClientContext context;
  ::google::protobuf::Empty request;
  GetIntersectionResponse response;
  ::grpc::Status status = stub->GetIntersection(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not retrieve intersection: " << status.error_code() << ": "
                << status.error_message();
  }
  for (auto item : response.values()) {
    values.push_back(item);
  }
  return values;
}

int main(int argc, char** argv) {
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  // Connect to the Oak Manager.
  std::unique_ptr<::oak::ManagerClient> manager_client = ::absl::make_unique<::oak::ManagerClient>(
      ::grpc::CreateChannel(FLAGS_manager_address, ::grpc::InsecureChannelCredentials()));

  // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string module_bytes = ::oak::utils::read_file(FLAGS_module);
  ::oak::CreateNodeResponse create_node_response = manager_client->CreateNode(module_bytes);

  std::stringstream addr;
  addr << "127.0.0.1:" << create_node_response.port();
  LOG(INFO) << "Connecting to Oak Node: " << addr.str();

  ::oak::NodeClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Node from different clients.
  auto stub_0 = PrivateSetIntersection::NewStub(::grpc::CreateChannel(
      addr.str(),
      ::asylo::EnclaveChannelCredentials(::asylo::BidirectionalNullCredentialsOptions())));

  auto stub_1 = PrivateSetIntersection::NewStub(::grpc::CreateChannel(
      addr.str(),
      ::asylo::EnclaveChannelCredentials(::asylo::BidirectionalNullCredentialsOptions())));

  // Submit sets from different clients.
  std::vector<std::string> set_0{"a", "b", "c"};
  SubmitSet(stub_0.get(), set_0);

  std::vector<std::string> set_1{"b", "c", "d"};
  SubmitSet(stub_1.get(), set_1);

  // Retrieve intersection.
  std::vector<std::string> intersection_0 = RetrieveIntersection(stub_0.get());
  LOG(INFO) << "client 0 intersection:";
  for (auto item : intersection_0) {
    LOG(INFO) << "- " << item;
  }

  std::vector<std::string> intersection_1 = RetrieveIntersection(stub_1.get());
  LOG(INFO) << "client 1 intersection:";
  for (auto item : intersection_1) {
    LOG(INFO) << "- " << item;
  }

  return 0;
}
