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
#include "examples/aggregator/proto/aggregator.grpc.pb.h"
#include "examples/aggregator/proto/aggregator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

using ::oak::examples::aggregator::Aggregator;
using ::oak::examples::aggregator::GetAggregationResponse;
using ::oak::examples::aggregator::SubmitSampleRequest;

void submit_sample(Aggregator::Stub* stub, std::vector<uint64_t> values) {
  grpc::ClientContext context;
  SubmitSampleRequest request;
  for (auto value : values) {
    request.add_values(value);
  }
  google::protobuf::Empty response;
  grpc::Status status = stub->SubmitSample(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not submit sample: " << status.error_code() << ": "
                << status.error_message();
  }
}

void get_aggregation(Aggregator::Stub* stub) {
  grpc::ClientContext context;
  google::protobuf::Empty request;
  GetAggregationResponse response;
  grpc::Status status = stub->GetAggregation(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not retrieve aggregation: " << status.error_code() << ": "
                << status.error_message();
  }
  if (!response.success()) {
    LOG(WARNING) << "Not enough samples have been aggregated";
    return;
  }

  LOG(INFO) << "Aggregation:";
  for (auto value : response.values()) {
    LOG(INFO) << "- " << value;
  }
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  auto stub = Aggregator::NewStub(oak::ApplicationClient::CreateChannel(address));

  // Submit samples from different clients.
  submit_sample(stub.get(), {0, 0, 10, 10, 0});
  submit_sample(stub.get(), {10, 10, 0, 0, 10});

  // Try to retrieve aggregation.
  get_aggregation(stub.get());

  // Submit final sample.
  submit_sample(stub.get(), {10, 10, 10, 10, 10});

  // Retrieve aggregation.
  get_aggregation(stub.get());

  return EXIT_SUCCESS;
}
