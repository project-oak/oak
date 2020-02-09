/*
 * Copyright 2020 The Project Oak Authors
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
#include "asylo/util/logging.h"
#include "examples/tensorflow/proto/tensorflow.grpc.pb.h"
#include "examples/tensorflow/proto/tensorflow.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

using ::oak::examples::tensorflow::InitRequest;
using ::oak::examples::tensorflow::InitResponse;
using ::oak::examples::tensorflow::Tensorflow;

void init_tensorflow(Tensorflow::Stub* stub) {
  grpc::ClientContext context;
  InitRequest request;
  InitResponse response;
  grpc::Status status = stub->InitTensorflow(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Error: " << status.error_code() << ": " << status.error_message();
    return;
  }
  LOG(INFO) << "Status: " << response.status();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = Tensorflow::NewStub(oak::ApplicationClient::CreateChannel(address));

  // Initialize TensorFlow in Oak.
  init_tensorflow(stub.get());

  return EXIT_SUCCESS;
}
