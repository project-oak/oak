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

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "examples/machine_learning/proto/machine_learning.grpc.pb.h"
#include "examples/machine_learning/proto/machine_learning.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/logging.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

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
    OAK_LOG(FATAL) << "Could not submit data: " << status.error_code() << ": "
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
    OAK_LOG(FATAL) << "Could not learn: " << status.error_code() << ": " << status.error_message();
  }
  return response.message();
}

std::string predict(MachineLearning::Stub* stub) {
  ::grpc::ClientContext context;
  MLPredict predict;
  MLResponse response;
  ::grpc::Status status = stub->Predict(&context, predict, &response);
  if (!status.ok()) {
    OAK_LOG(FATAL) << "Could not predict: " << status.error_code() << ": "
                   << status.error_message();
  }
  return response.message();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  OAK_LOG(INFO) << "Connecting to Oak Application: " << address;

  // Connect to the Oak Application.
  auto stub = MachineLearning::NewStub(oak::ApplicationClient::CreateTlsChannel(address, ca_cert));

  // Perform multiple invocations of the same Oak Application, with different parameters.
  auto message_0 = send_data(stub.get());
  OAK_LOG(INFO) << "data response: " << message_0;

  auto message_1 = learn(stub.get());
  OAK_LOG(INFO) << "learn response: " << message_1;

  auto message_2 = predict(stub.get());
  OAK_LOG(INFO) << "predict response: " << message_2;

  return EXIT_SUCCESS;
}
