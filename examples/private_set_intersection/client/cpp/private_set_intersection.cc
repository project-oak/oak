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
ABSL_FLAG(std::string, set_id, "", "ID of the set intersection");
ABSL_FLAG(std::string, ca_cert_path, "", "Path to the PEM-encoded CA root certificate");
ABSL_FLAG(std::string, public_key, "", "Path to the PEM-encoded public key used as a data label");

using ::oak::examples::private_set_intersection::GetIntersectionRequest;
using ::oak::examples::private_set_intersection::GetIntersectionResponse;
using ::oak::examples::private_set_intersection::PrivateSetIntersection;
using ::oak::examples::private_set_intersection::SubmitSetRequest;

grpc::Status SubmitSet(PrivateSetIntersection::Stub* stub, std::string set_id,
                       std::vector<std::string> set) {
  grpc::ClientContext context;
  SubmitSetRequest request;
  request.set_set_id(set_id);
  for (auto item : set) {
    request.add_values(item);
  }
  google::protobuf::Empty response;
  return stub->SubmitSet(&context, request, &response);
}

std::vector<std::string> RetrieveIntersection(PrivateSetIntersection::Stub* stub,
                                              std::string set_id) {
  std::vector<std::string> values;
  grpc::ClientContext context;
  GetIntersectionRequest request;
  request.set_set_id(set_id);
  GetIntersectionResponse response;
  grpc::Status status = stub->GetIntersection(&context, request, &response);
  if (!status.ok()) {
    LOG(FATAL) << "Could not retrieve intersection: "
               << oak::status_code_to_string(status.error_code()) << ": " << status.error_message();
  }
  for (auto item : response.values()) {
    values.push_back(item);
  }
  return values;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string set_id = absl::GetFlag(FLAGS_set_id);
  std::string ca_cert_path =
      oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert_path));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Use a more restrictive Label, based on a bearer token shared between the two
  // clients.
  std::string public_key = oak::ApplicationClient::LoadPublicKey(absl::GetFlag(FLAGS_public_key));
  oak::label::Label label = oak::WebAssemblyModuleSignatureLabel(public_key);

  auto stub_0 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), label));

  auto stub_1 = PrivateSetIntersection::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), label));

  // Submit sets from different clients.
  std::vector<std::string> set_0{"a", "b", "c"};
  auto submit_status_0 = SubmitSet(stub_0.get(), set_id, set_0);
  if (!submit_status_0.ok()) {
    LOG(FATAL) << "Could not submit set: " << submit_status_0.error_code() << ": "
               << submit_status_0.error_message();
  }

  std::vector<std::string> set_1{"b", "c", "d"};
  auto submit_status_1 = SubmitSet(stub_1.get(), set_id, set_1);
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
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), invalid_label));
  std::vector<std::string> set_2{"c", "d", "e"};
  auto submit_status_2 = SubmitSet(invalid_stub.get(), set_id, set_2);
  // Error code `3` means `could not process gRPC request`.
  if (submit_status_2.error_code() != 3) {
    LOG(FATAL) << "Invalid public key was accepted";
  }

  // Retrieve intersection.
  std::set<std::string> expected_set{"b", "c"};
  std::vector<std::string> intersection_0 = RetrieveIntersection(stub_0.get(), set_id);
  LOG(INFO) << "client 0 intersection:";
  for (auto item : intersection_0) {
    LOG(INFO) << "- " << item;
  }
  if (std::set<std::string>(intersection_0.begin(), intersection_0.end()) != expected_set) {
    LOG(FATAL) << "Unexpected set";
  }

  std::vector<std::string> intersection_1 = RetrieveIntersection(stub_1.get(), set_id);
  LOG(INFO) << "client 1 intersection:";
  for (auto item : intersection_1) {
    LOG(INFO) << "- " << item;
  }
  if (std::set<std::string>(intersection_1.begin(), intersection_1.end()) != expected_set) {
    LOG(FATAL) << "Unexpected set";
  }

  return EXIT_SUCCESS;
}
