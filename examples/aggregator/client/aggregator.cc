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

#include <cassert>
#include <optional>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "asylo/util/logging.h"
#include "examples/aggregator/proto/aggregator.grpc.pb.h"
#include "examples/aggregator/proto/aggregator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

using ::oak::examples::aggregator::Aggregator;
using ::oak::examples::aggregator::Vector;

void submit_sample(Aggregator::Stub* stub, std::vector<uint64_t> values) {
  grpc::ClientContext context;
  Vector request;
  for (auto value : values) {
    request.add_items(value);
  }
  google::protobuf::Empty response;
  grpc::Status status = stub->SubmitSample(&context, request, &response);
  if (!status.ok()) {
    LOG(QFATAL) << "Could not submit sample: " << status.error_code() << ": "
                << status.error_message();
  }
}

std::optional<std::vector<uint64_t>> get_aggregation(Aggregator::Stub* stub) {
  std::vector<uint64_t> items;
  grpc::ClientContext context;
  google::protobuf::Empty request;
  Vector response;
  grpc::Status status = stub->GetCurrentValue(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not get current value: " << status.error_code() << ": "
                 << status.error_message();
    return std::nullopt;
  }

  LOG(INFO) << "Aggregation:";
  for (auto item : response.items()) {
    LOG(INFO) << "- " << item;
    items.push_back(item);
  }
  return items;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  auto stub = Aggregator::NewStub(oak::ApplicationClient::CreateChannel(address));

  // Submit initial samples.
  submit_sample(stub.get(), {0, 0, 10, 10, 0});
  submit_sample(stub.get(), {10, 10, 0, 0, 10});

  // Try to retrieve aggregation.
  auto first_result = get_aggregation(stub.get());
  assert(!first_result);

  // Submit final sample.
  submit_sample(stub.get(), {10, 10, 10, 10, 10});

  // Retrieve aggregation.
  auto second_result = get_aggregation(stub.get());
  assert(std::vector<uint64_t>(5, 20) == second_result);

  return EXIT_SUCCESS;
}
