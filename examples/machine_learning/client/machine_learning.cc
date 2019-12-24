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

#include <cstdlib>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "examples/machine_learning/proto/machine_learning.grpc.pb.h"
#include "examples/machine_learning/proto/machine_learning.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/client/manager_client.h"
#include "oak/common/utils.h"

ABSL_FLAG(std::string, manager_address, "127.0.0.1:8888",
          "Address of the Oak Manager to connect to");
ABSL_FLAG(std::string, module, "", "File containing the compiled WebAssembly module");

using ::oak::examples::machine_learning::MachineLearning;
using ::oak::examples::machine_learning::MLData;
using ::oak::examples::machine_learning::MLLearn;
using ::oak::examples::machine_learning::MLPredict;
using ::oak::examples::machine_learning::MLResponse;

std::string send_data(MachineLearning::Stub* stub) {
  ::grpc::ClientContext context;
  MLData data;
  // FIXME: set data here
  MLResponse response;
  ::grpc::Status status = stub->Data(&context, data, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not submit data: " << status.error_code() << ": "
                << status.error_message();
  }
  return response.message();
}

std::string learn(MachineLearning::Stub* stub) {
  ::grpc::ClientContext context;
  MLLearn learn;
  MLResponse response;
  ::grpc::Status status = stub->Learn(&context, learn, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not learn: " << status.error_code() << ": " << status.error_message();
  }
  return response.message();
}

std::string predict(MachineLearning::Stub* stub) {
  ::grpc::ClientContext context;
  MLPredict predict;
  MLResponse response;
  ::grpc::Status status = stub->Predict(&context, predict, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not predict: " << status.error_code() << ": " << status.error_message();
  }
  return response.message();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  // Connect to the Oak Manager.
  std::unique_ptr<oak::ManagerClient> manager_client =
      ::absl::make_unique<::oak::ManagerClient>(::grpc::CreateChannel(
          absl::GetFlag(FLAGS_manager_address), ::grpc::InsecureChannelCredentials()));

  // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string module_bytes = ::oak::utils::read_file(absl::GetFlag(FLAGS_module));
  std::unique_ptr<oak::CreateApplicationResponse> create_application_response =
      manager_client->CreateApplication(module_bytes);
  if (create_application_response == nullptr) {
    LOG(QFATAL) << "Failed to create application";
  }

  std::stringstream addr;
  addr << "127.0.0.1:" << create_application_response->grpc_port();
  LOG(INFO) << "Connecting to Oak Application: " << addr.str();

  ::oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = MachineLearning::NewStub(oak::ApplicationClient::CreateChannel(addr.str()));

  // Perform multiple invocations of the same Oak Application, with different parameters.
  auto message_0 = send_data(stub.get());
  LOG(INFO) << "data response: " << message_0;

  auto message_1 = learn(stub.get());
  LOG(INFO) << "learn response: " << message_1;

  auto message_2 = predict(stub.get());
  LOG(INFO) << "predict response: " << message_2;

  return EXIT_SUCCESS;
}
