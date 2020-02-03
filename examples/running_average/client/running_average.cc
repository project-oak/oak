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
#include "examples/running_average/proto/running_average.grpc.pb.h"
#include "examples/running_average/proto/running_average.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/utils.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

using ::oak::examples::running_average::GetAverageResponse;
using ::oak::examples::running_average::RunningAverage;
using ::oak::examples::running_average::SubmitSampleRequest;

void submit_sample(RunningAverage::Stub* stub, int sample_value) {
  grpc::ClientContext context;
  SubmitSampleRequest request;
  request.set_value(sample_value);
  google::protobuf::Empty response;
  grpc::Status status = stub->SubmitSample(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not submit sample: " << status.error_code() << ": "
                << status.error_message();
  }
}

int retrieve_average(RunningAverage::Stub* stub) {
  grpc::ClientContext context;
  google::protobuf::Empty request;
  GetAverageResponse response;
  grpc::Status status = stub->GetAverage(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not retrieve average: " << status.error_code() << ": "
                << status.error_message();
  }
  return response.average();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  oak::ApplicationClient::InitializeAssertionAuthorities();

  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // Connect to the newly created Oak Application from different clients sharing the same access
  // token.
  oak::NonceGenerator<oak::kPerChannelNonceSizeBytes> nonce_generator;
  std::string authorization_bearer_token = oak::NonceToBytes(nonce_generator.NextNonce());

  auto stub_0 = RunningAverage::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::authorization_bearer_token_call_credentials(
                      authorization_bearer_token)));

  auto stub_1 = RunningAverage::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::authorization_bearer_token_call_credentials(
                      authorization_bearer_token)));

  // Submit samples from different clients.
  submit_sample(stub_0.get(), 100);
  submit_sample(stub_1.get(), 200);
  submit_sample(stub_0.get(), 40);
  submit_sample(stub_1.get(), 60);

  // Retrieve average.
  int average_0 = retrieve_average(stub_0.get());
  LOG(INFO) << "client 0 average: " << average_0;

  int average_1 = retrieve_average(stub_1.get());
  LOG(INFO) << "client 1 average: " << average_1;

  return EXIT_SUCCESS;
}
