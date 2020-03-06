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
#include "examples/private_set_intersection/proto/private_set_intersection.grpc.pb.h"
#include "examples/private_set_intersection/proto/private_set_intersection.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/logging.h"
#include "oak/common/nonce_generator.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

using ::oak::examples::private_set_intersection::GetIntersectionResponse;
using ::oak::examples::private_set_intersection::PrivateSetIntersection;
using ::oak::examples::private_set_intersection::SubmitSetRequest;

void SubmitSet(PrivateSetIntersection::Stub* stub, std::vector<std::string> set) {
  grpc::ClientContext context;
  SubmitSetRequest request;
  for (auto item : set) {
    request.add_values(item);
  }
  google::protobuf::Empty response;
  grpc::Status status = stub->SubmitSet(&context, request, &response);
  if (!status.ok()) {
    OAK_LOG(QFATAL) << "Could not submit set: " << status.error_code() << ": "
                    << status.error_message();
  }
}

std::vector<std::string> RetrieveIntersection(PrivateSetIntersection::Stub* stub) {
  std::vector<std::string> values;
  grpc::ClientContext context;
  google::protobuf::Empty request;
  GetIntersectionResponse response;
  grpc::Status status = stub->GetIntersection(&context, request, &response);
  if (!status.ok()) {
    OAK_LOG(QFATAL) << "Could not retrieve intersection: " << status.error_code() << ": "
                    << status.error_message();
  }
  for (auto item : response.values()) {
    values.push_back(item);
  }
  return values;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  OAK_LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the Oak Application from different clients sharing the same access token.
  oak::NonceGenerator<oak::kPerChannelNonceSizeBytes> nonce_generator;
  std::string authorization_bearer_token = oak::NonceToBytes(nonce_generator.NextNonce());

  auto stub_0 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::authorization_bearer_token_call_credentials(
                   authorization_bearer_token)));

  auto stub_1 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::authorization_bearer_token_call_credentials(
                   authorization_bearer_token)));

  // Submit sets from different clients.
  std::vector<std::string> set_0{"a", "b", "c"};
  SubmitSet(stub_0.get(), set_0);

  std::vector<std::string> set_1{"b", "c", "d"};
  SubmitSet(stub_1.get(), set_1);

  // Retrieve intersection.
  std::vector<std::string> intersection_0 = RetrieveIntersection(stub_0.get());
  OAK_LOG(INFO) << "client 0 intersection:";
  for (auto item : intersection_0) {
    OAK_LOG(INFO) << "- " << item;
  }

  std::vector<std::string> intersection_1 = RetrieveIntersection(stub_1.get());
  OAK_LOG(INFO) << "client 1 intersection:";
  for (auto item : intersection_1) {
    OAK_LOG(INFO) << "- " << item;
  }

  return EXIT_SUCCESS;
}
