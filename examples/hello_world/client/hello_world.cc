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
#include "examples/hello_world/proto/hello_world.grpc.pb.h"
#include "examples/hello_world/proto/hello_world.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

using ::oak::examples::hello_world::HelloRequest;
using ::oak::examples::hello_world::HelloResponse;
using ::oak::examples::hello_world::HelloWorld;

void say_hello(HelloWorld::Stub* stub, std::string name) {
  grpc::ClientContext context;
  HelloRequest request;
  request.set_greeting(name);
  LOG(INFO) << "Request: " << request.greeting();
  HelloResponse response;
  grpc::Status status = stub->SayHello(&context, request, &response);
  if (!status.ok()) {
    LOG(FATAL) << "Could not call SayHello('" << name << "'): " << status.error_code() << ": "
               << status.error_message();
  }
  LOG(INFO) << "Response: " << response.reply();
}

void lots_of_replies(HelloWorld::Stub* stub, std::string name) {
  grpc::ClientContext context;
  HelloRequest request;
  request.set_greeting(name);
  LOG(INFO) << "Request: " << request.greeting();
  auto reader = stub->LotsOfReplies(&context, request);
  if (reader == nullptr) {
    LOG(FATAL) << "Could not call LotsOfReplies";
  }
  HelloResponse response;
  while (reader->Read(&response)) {
    LOG(INFO) << "Response: " << response.reply();
  }
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // Connect to the Oak Application.
  auto stub = HelloWorld::NewStub(oak::ApplicationClient::CreateTlsChannel(address, ca_cert));

  // Perform multiple invocations of the same Oak Application, with different parameters.
  say_hello(stub.get(), "WORLD");
  say_hello(stub.get(), "MONDO");
  say_hello(stub.get(), "世界");
  say_hello(stub.get(), "MONDE");

  lots_of_replies(stub.get(), "WORLDS");

  return EXIT_SUCCESS;
}
