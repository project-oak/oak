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
#include "examples/trusted_database/proto/trusted_database.grpc.pb.h"
#include "examples/trusted_database/proto/trusted_database.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert_path, "", "Path to the PEM-encoded CA root certificate");
ABSL_FLAG(float, latitude, float{}, "Requested location's latitude in degrees (WGS84)");
ABSL_FLAG(float, longitude, float{}, "Requested location's longitude in degrees (WGS84)");

using ::oak::examples::trusted_database::ListPointsOfInterestRequest;
using ::oak::examples::trusted_database::ListPointsOfInterestResponse;
using ::oak::examples::trusted_database::Location;
using ::oak::examples::trusted_database::PointOfInterest;
using ::oak::examples::trusted_database::TrustedDatabase;

void get_nearest_point_of_interest(TrustedDatabase::Stub* stub, float latitude, float longitude) {
  grpc::ClientContext context;
  LOG(INFO) << "Getting nearest point of interest:";
  ListPointsOfInterestRequest request;
  Location* location = request.mutable_location();
  location->set_latitude_degrees(latitude);
  location->set_longitude_degrees(longitude);
  ListPointsOfInterestResponse response;
  grpc::Status status = stub->ListPointsOfInterest(&context, request, &response);
  if (!status.ok()) {
    LOG(ERROR) << "Could not get nearest point of interest: " << status.error_code() << ": "
               << status.error_message();
  }
  LOG(INFO) << "Response:";
  LOG(INFO) << " - name: " << response.point_of_interest().name();
  LOG(INFO) << " - latitude: " << response.point_of_interest().location().latitude_degrees();
  LOG(INFO) << " - longitude: " << response.point_of_interest().location().longitude_degrees();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert_path =
      oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert_path));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Use a more restrictive Label.
  oak::label::Label label = oak::PublicUntrustedLabel();
  // Connect to the Oak Application.
  auto stub = TrustedDatabase::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), label));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  // Parse arguments.
  float latitude = absl::GetFlag(FLAGS_latitude);
  if (latitude < -90.0 || latitude > 90.0) {
    LOG(FATAL) << "Latitude must be a valid floating point number >=-90 and <= 90, found "
               << latitude;
  }
  float longitude = absl::GetFlag(FLAGS_longitude);
  if (longitude < -180.0 || longitude > 180.0) {
    LOG(FATAL) << "Longitude must be a valid floating point number >= -180 and <= 180, found "
               << longitude;
  }

  // Get nearest point of interest from the server.
  get_nearest_point_of_interest(stub.get(), latitude, longitude);

  return EXIT_SUCCESS;
}
