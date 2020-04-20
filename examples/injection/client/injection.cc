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
#include "examples/injection/proto/injection.grpc.pb.h"
#include "examples/injection/proto/injection.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/label.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::injection::BlobResponse;
using ::oak::examples::injection::BlobStore;
using ::oak::examples::injection::GetBlobRequest;
using ::oak::examples::injection::PutBlobRequest;

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Use a more restrictive Label.
  oak::label::Label label = oak::PublicUntrustedLabel();
  // Connect to the Oak Application.
  auto stub = BlobStore::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  PutBlobRequest putRequest;
  putRequest.set_blob("Hello, blob store!");
  grpc::ClientContext putContext;
  BlobResponse putResponse;
  grpc::Status putStatus = stub->PutBlob(&putContext, putRequest, &putResponse);
  if (!putStatus.ok()) {
    LOG(FATAL) << "PutBlob failed: " << putStatus.error_code() << ": " << putStatus.error_message();
  }
  LOG(INFO) << "Blob stored at id: " << putResponse.id();

  GetBlobRequest getRequest;
  getRequest.set_id(putResponse.id());
  grpc::ClientContext getContext;
  BlobResponse getResponse;
  grpc::Status getStatus = stub->GetBlob(&getContext, getRequest, &getResponse);
  if (!getStatus.ok()) {
    LOG(FATAL) << "GetBlob failed: " << getStatus.error_code() << ": " << getStatus.error_message();
  }
  LOG(INFO) << "Successfully retrieved Blob";

  if (putRequest.blob() != getResponse.blob()) {
    LOG(FATAL) << "Blobs were different. Original: '" << putRequest.blob() << "', retrieved: '"
               << getResponse.blob() << "'";
  }
  LOG(INFO) << "Blobs match!";

  return EXIT_SUCCESS;
}
