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
#include "examples/private_information_retrieval/proto/private_information_retrieval.grpc.pb.h"
#include "examples/private_information_retrieval/proto/private_information_retrieval.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::vector<std::string>, location, std::vector<std::string>{},
          "Requested location (latitude and longitude separated by comma)");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::private_information_retrieval::Location;
using ::oak::examples::private_information_retrieval::PointOfInterest;
using ::oak::examples::private_information_retrieval::PrivateInformationRetrieval;

void get_nearest_point_of_interest(PrivateInformationRetrieval::Stub* stub, float latitude,
                                   float longitude) {
  grpc::ClientContext context;
  LOG(INFO) << "Getting nearest point of interest:";
  Location request;
  request.set_latitude(latitude);
  request.set_longitude(longitude);
  PointOfInterest response;
  grpc::Status status = stub->GetNearestPointOfInterest(&context, request, &response);
  if (!status.ok()) {
    LOG(ERROR) << "Could not get nearest point of interest: " << status.error_code() << ": "
               << status.error_message();
  }
  LOG(INFO) << "Response:";
  LOG(INFO) << " - name: " << response.name();
  LOG(INFO) << " - latitude: " << response.location().latitude();
  LOG(INFO) << " - longitude: " << response.location().longitude();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  auto stub = PrivateInformationRetrieval::NewStub(
      oak::ApplicationClient::CreateTlsChannel(address, ca_cert));

  // Parse arguments.
  auto location = absl::GetFlag(FLAGS_location);
  if (location.size() != 2) {
    LOG(FATAL) << "Incorrect number of coordinates: " << location.size() << " (expected 2)";
  }
  float latitude;
  if (!absl::SimpleAtof(location.front(), &latitude)) {
    LOG(FATAL) << "Incorrect latitude: " << location.front();
  }
  float longitude;
  if (!absl::SimpleAtof(location.back(), &longitude)) {
    LOG(FATAL) << "Incorrect longitude: " << location.back();
  }

  // Get nearest point of interest from the server.
  get_nearest_point_of_interest(stub.get(), latitude, longitude);

  return EXIT_SUCCESS;
}
