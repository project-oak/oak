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
#include "experiments/tls-over-grpc/service_impl.h"
#include "grpcpp/grpcpp.h"

ABSL_FLAG(std::string, port, "8080", "Port for the server to listen on");
ABSL_FLAG(std::string, server_key, "experiments/tls-over-grpc/server.key",
          "Path to the server key");
ABSL_FLAG(std::string, server_cert, "experiments/tls-over-grpc/server.pem",
          "Path to the server certificate");
ABSL_FLAG(std::string, client_cert, "experiments/tls-over-grpc/client.pem",
          "Path to the client certificate");

void RunServer() {
  std::string server_address = absl::StrCat("[::]:", absl::GetFlag(FLAGS_port));
  absl::StatusOr<
      std::unique_ptr<experiments::tls_over_grpc::TlsOverGrpcServiceImpl>>
      service = experiments::tls_over_grpc::TlsOverGrpcServiceImpl::Create(
          absl::GetFlag(FLAGS_server_key), absl::GetFlag(FLAGS_server_cert),
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

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  RunServer();
  return 0;
}
