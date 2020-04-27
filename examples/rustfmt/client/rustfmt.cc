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
#include "examples/rustfmt/proto/rustfmt.grpc.pb.h"
#include "examples/rustfmt/proto/rustfmt.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::rustfmt::FormatRequest;
using ::oak::examples::rustfmt::FormatResponse;
using ::oak::examples::rustfmt::FormatService;

void format(FormatService::Stub* stub, std::string code) {
  FormatRequest request;
  request.set_code(code);
  LOG(INFO) << "Request: " << request.code();
  grpc::ClientContext context;
  FormatResponse response;
  grpc::Status status = stub->Format(&context, request, &response);
  if (!status.ok()) {
    LOG(FATAL) << "Could not call Format: " << status.error_code() << ": "
               << status.error_message();
  }
  LOG(INFO) << "Response: " << response.code();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // Connect to the Oak Application.
  auto stub = FormatService::NewStub(oak::ApplicationClient::CreateTlsChannel(address, ca_cert));

  // Perform multiple invocations of the same Oak Application, with different parameters.
  format(stub.get(), "fn     main    ()     {     }");
  format(stub.get(), "enum Foo{A,B}");

  return EXIT_SUCCESS;
}
