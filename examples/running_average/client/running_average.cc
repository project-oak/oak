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
#include "examples/running_average/proto/running_average.grpc.pb.h"
#include "examples/running_average/proto/running_average.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/nonce_generator.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

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
    LOG(FATAL) << "Could not submit sample: " << status.error_code() << ": "
               << status.error_message();
  }
}

int retrieve_average(RunningAverage::Stub* stub) {
  grpc::ClientContext context;
  google::protobuf::Empty request;
  GetAverageResponse response;
  grpc::Status status = stub->GetAverage(&context, request, &response);
  if (!status.ok()) {
    LOG(FATAL) << "Could not retrieve average: " << status.error_code() << ": "
               << status.error_message();
  }
  return response.average();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // Connect to the Oak Application from different clients sharing the same access token.
  oak::NonceGenerator<oak::kPerChannelNonceSizeBytes> nonce_generator;
  std::string authorization_bearer_token = oak::NonceToBytes(nonce_generator.NextNonce());

  // TODO(#1066): Use a more restrictive Label, based on a bearer token shared between the two
  // clients.
  oak::label::Label label = oak::PublicUntrustedLabel();

  auto stub_0 = RunningAverage::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub_0 == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  auto stub_1 = RunningAverage::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub_1 == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  // Submit samples from different clients.
  submit_sample(stub_0.get(), 100);
  submit_sample(stub_1.get(), 200);
  submit_sample(stub_0.get(), 40);
  submit_sample(stub_1.get(), 60);

  // Retrieve average.
  int average_0 = retrieve_average(stub_0.get());
  LOG(INFO) << "Client 0 average: " << average_0;
  if (average_0 != 100) {
    LOG(FATAL) << "Unexpected average: " << average_0;
  }

  int average_1 = retrieve_average(stub_1.get());
  LOG(INFO) << "Client 1 average: " << average_1;
  if (average_1 != 100) {
    LOG(FATAL) << "Unexpected average: " << average_0;
  }

  return EXIT_SUCCESS;
}
