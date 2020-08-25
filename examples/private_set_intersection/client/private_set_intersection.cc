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
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/nonce_generator.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::private_set_intersection::GetIntersectionResponse;
using ::oak::examples::private_set_intersection::PrivateSetIntersection;
using ::oak::examples::private_set_intersection::SubmitSetRequest;

grpc::Status SubmitSet(PrivateSetIntersection::Stub* stub, std::vector<std::string> set) {
  grpc::ClientContext context;
  SubmitSetRequest request;
  for (auto item : set) {
    request.add_values(item);
  }
  google::protobuf::Empty response;
  return stub->SubmitSet(&context, request, &response);
}

std::vector<std::string> RetrieveIntersection(PrivateSetIntersection::Stub* stub) {
  std::vector<std::string> values;
  grpc::ClientContext context;
  google::protobuf::Empty request;
  GetIntersectionResponse response;
  grpc::Status status = stub->GetIntersection(&context, request, &response);
  if (!status.ok()) {
    LOG(FATAL) << "Could not retrieve intersection: " << status.error_code() << ": "
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
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Use a more restrictive Label, based on a bearer token shared between the two
  // clients.
  // Public key is stored in the `examples/keys/ed25519/test.pub` file.
  std::string public_key_base64 = "f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=";
  std::string public_key;
  if (!absl::Base64Unescape(public_key_base64, &public_key)) {
    LOG(FATAL) << "Could not decode public key: " << public_key_base64;
  }
  oak::label::Label label = oak::WebAssemblyModuleSignatureLabel(public_key);

  auto stub_0 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));

  auto stub_1 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));

  // Submit sets from different clients.
  std::vector<std::string> set_0{"a", "b", "c"};
  auto submit_status_0 = SubmitSet(stub_0.get(), set_0);
  if (!submit_status_0.ok()) {
    LOG(FATAL) << "Could not submit set: " << submit_status_0.error_code() << ": "
               << submit_status_0.error_message();
  }

  std::vector<std::string> set_1{"b", "c", "d"};
  auto submit_status_1 = SubmitSet(stub_1.get(), set_1);
  if (!submit_status_1.ok()) {
    LOG(FATAL) << "Could not submit set: " << submit_status_1.error_code() << ": "
               << submit_status_1.error_message();
  }

  // Use an invalid public key.
  std::string invalid_public_key_base64 = "vpxqTZOUq1FjcaB9uJYCuv4kAg+AsgMwubA6WE+2pmk=";
  std::string invalid_public_key;
  if (!absl::Base64Unescape(invalid_public_key_base64, &invalid_public_key)) {
    LOG(FATAL) << "Could not decode public key: " << invalid_public_key_base64;
  }
  oak::label::Label invalid_label = oak::WebAssemblyModuleSignatureLabel(invalid_public_key);
  auto invalid_stub = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), invalid_label));
  std::vector<std::string> set_2{"c", "d", "e"};
  auto submit_status_2 = SubmitSet(invalid_stub.get(), set_2);
  if (submit_status_2.ok()) {
    LOG(FATAL) << "Invalid public key was accepted";
  }

  // Retrieve intersection.
  std::set<std::string> expected_set{"b", "c"};
  std::vector<std::string> intersection_0 = RetrieveIntersection(stub_0.get());
  LOG(INFO) << "client 0 intersection:";
  for (auto item : intersection_0) {
    LOG(INFO) << "- " << item;
  }
  if (std::set<std::string>(intersection_0.begin(), intersection_0.end()) != expected_set) {
    LOG(FATAL) << "Unexpected set";
  }

  std::vector<std::string> intersection_1 = RetrieveIntersection(stub_1.get());
  LOG(INFO) << "client 1 intersection:";
  for (auto item : intersection_1) {
    LOG(INFO) << "- " << item;
  }
  if (std::set<std::string>(intersection_1.begin(), intersection_1.end()) != expected_set) {
    LOG(FATAL) << "Unexpected set";
  }

  return EXIT_SUCCESS;
}
