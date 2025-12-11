/*
 * Copyright 2024 The Project Oak Authors
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

#include <iostream>
#include <memory>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "grpcpp/grpcpp.h"
#include "oak_session/tls/example/grpc/service_impl.h"
#include "oak_session/tls/util.h"

ABSL_FLAG(std::string, port, "8080", "Port for the server to listen on");
ABSL_FLAG(std::string, server_key, "oak_session/tls/testing/server.key",
          "Path to the server key");
ABSL_FLAG(std::string, server_cert, "oak_session/tls/testing/server.pem",
          "Path to the server certificate");
ABSL_FLAG(std::string, client_cert, "oak_session/tls/testing/client.pem",
          "Path to the client certificate");

namespace oak::session::tls::example {
void RunServer() {
  std::string server_address = absl::StrCat("[::]:", absl::GetFlag(FLAGS_port));

  auto server_key =
      util::LoadPrivateKeyFromFile(absl::GetFlag(FLAGS_server_key).c_str());
  if (!server_key.ok()) {
    LOG(FATAL) << "Failed to load server key: " << server_key.status();
  }
  auto server_cert =
      util::LoadCertificateFromFile(absl::GetFlag(FLAGS_server_cert).c_str());
  if (!server_cert.ok()) {
    LOG(FATAL) << "Failed to load server certificate: " << server_cert.status();
  }

  absl::StatusOr<std::unique_ptr<TlsOverGrpcServiceImpl>> service =
      TlsOverGrpcServiceImpl::Create(*server_key, *server_cert,
                                     absl::GetFlag(FLAGS_client_cert));
  if (!service.ok()) {
    LOG(FATAL) << "Failed to create service: " << service.status();
  }

  grpc::ServerBuilder builder;
  int selected_port;
  builder.AddListeningPort(server_address, grpc::InsecureServerCredentials(),
                           &selected_port);
  builder.RegisterService(service->get());

  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  LOG(INFO) << "Server listening on port " << selected_port;

  server->Wait();
}
}  // namespace oak::session::tls::example

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  oak::session::tls::example::RunServer();
  return 0;
}
