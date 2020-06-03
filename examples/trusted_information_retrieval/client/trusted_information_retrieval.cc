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
#include "examples/trusted_information_retrieval/proto/trusted_information_retrieval.grpc.pb.h"
#include "examples/trusted_information_retrieval/proto/trusted_information_retrieval.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::vector<std::string>, location, std::vector<std::string>{},
          "Requested location (latitude and longitude separated by comma)");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::trusted_information_retrieval::ListPointsOfInterestRequest;
using ::oak::examples::trusted_information_retrieval::ListPointsOfInterestResponse;
using ::oak::examples::trusted_information_retrieval::Location;
using ::oak::examples::trusted_information_retrieval::PointOfInterest;
using ::oak::examples::trusted_information_retrieval::TrustedInformationRetrieval;

void get_nearest_point_of_interest(TrustedInformationRetrieval::Stub* stub, float latitude,
                                   float longitude) {
  grpc::ClientContext context;
  LOG(INFO) << "Getting nearest point of interest:";
  ListPointsOfInterestRequest request;
  Location* location = request.mutable_location();
  location->set_latitude(latitude);
  location->set_longitude(longitude);
  ListPointsOfInterestResponse response;
  grpc::Status status = stub->ListPointsOfInterest(&context, request, &response);
  if (!status.ok()) {
    LOG(ERROR) << "Could not get nearest point of interest: " << status.error_code() << ": "
               << status.error_message();
  }
  LOG(INFO) << "Response:";
  LOG(INFO) << " - name: " << response.point_of_interest().name();
  LOG(INFO) << " - latitude: " << response.point_of_interest().location().latitude();
  LOG(INFO) << " - longitude: " << response.point_of_interest().location().longitude();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Use a more restrictive Label.
  oak::label::Label label = oak::PublicUntrustedLabel();
  // Connect to the Oak Application.
  auto stub = TrustedInformationRetrieval::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  // Parse arguments.
  auto location = absl::GetFlag(FLAGS_location);
  if (location.size() != 2) {
    LOG(FATAL) << "Incorrect number of coordinates: " << location.size() << " (expected 2)";
  }
  float latitude;
  if (!absl::SimpleAtof(location.front(), &latitude) && latitude >= -90.0 && latitude <= 90.0) {
    LOG(FATAL) << "Latitude must be a valid floating point number >=-90 and <= 90.";
  }
  float longitude;
  if (!absl::SimpleAtof(location.back(), &longitude) && longitude >= -180.0 && longitude <= 180.0) {
    LOG(FATAL) << "Longitude must be a valid floating point number >= -180 and <= 180.";
  }

  // Get nearest point of interest from the server.
  get_nearest_point_of_interest(stub.get(), latitude, longitude);

  return EXIT_SUCCESS;
}
