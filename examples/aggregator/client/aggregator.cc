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
#include "absl/strings/numbers.h"
#include "absl/strings/str_split.h"
#include "absl/types/optional.h"
#include "examples/aggregator/proto/aggregator.grpc.pb.h"
#include "examples/aggregator/proto/aggregator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/logging.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, bucket, "", "Bucket under which to aggregate samples");
ABSL_FLAG(
    std::vector<std::string>, data, std::vector<std::string>{},
    "A comma-separated list of `index:value` entries that represent a single sparse vector sample");

using ::oak::examples::aggregator::Aggregator;
using ::oak::examples::aggregator::Sample;
using ::oak::examples::aggregator::SerializedSparseVector;

void submit_sample(Aggregator::Stub* stub, std::string& bucket, std::vector<uint32_t>& indices,
                   std::vector<float>& values) {
  grpc::ClientContext context;
  OAK_LOG(INFO) << "Submitting sample:";
  Sample request;
  OAK_LOG(INFO) << "  bucket: " << bucket;
  request.set_bucket(bucket);
  OAK_LOG(INFO) << "  indices:";
  for (auto index : indices) {
    OAK_LOG(INFO) << "    - " << index;
    request.mutable_data()->add_indices(index);
  }
  OAK_LOG(INFO) << "  values:";
  for (auto value : values) {
    OAK_LOG(INFO) << "    - " << value;
    request.mutable_data()->add_values(value);
  }
  google::protobuf::Empty response;
  grpc::Status status = stub->SubmitSample(&context, request, &response);
  if (!status.ok()) {
    OAK_LOG(ERROR) << "Could not submit sample: " << status.error_code() << ": "
                   << status.error_message();
  }
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  OAK_LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  auto stub = Aggregator::NewStub(oak::ApplicationClient::CreateChannel(address));

  // Parse arguments.
  auto bucket = absl::GetFlag(FLAGS_bucket);
  std::vector<uint32_t> indices;
  std::vector<float> values;
  for (const std::string& item : absl::GetFlag(FLAGS_data)) {
    std::vector<std::string> item_pair = absl::StrSplit(item, ':');
    if (item_pair.size() != 2) {
      OAK_LOG(QFATAL) << "Incorrect data specification: " << item;
    }

    uint32_t index;
    if (!absl::SimpleAtoi(item_pair.front(), &index)) {
      OAK_LOG(QFATAL) << "Incorrect index: " << item_pair.front();
    }
    indices.push_back(index);

    float value;
    if (!absl::SimpleAtof(item_pair.back(), &value)) {
      OAK_LOG(QFATAL) << "Incorrect value: " << item_pair.back();
    }
    values.push_back(value);
  }

  // Submit data sample.
  submit_sample(stub.get(), bucket, indices, values);

  return EXIT_SUCCESS;
}
