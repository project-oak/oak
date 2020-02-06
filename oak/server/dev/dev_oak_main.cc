/*
 * Copyright 2018 The Project Oak Authors
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

#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/util/logging.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/server/dev/dev_oak_manager.h"

ABSL_FLAG(int, grpc_port, 8888, "Port to listen on");

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // Create manager instance.
  std::unique_ptr<oak::Manager::Service> service = absl::make_unique<oak::DevOakManager>();

  // Initialize and run gRPC server.
  int selected_port = absl::GetFlag(FLAGS_grpc_port);
  std::string addr = "[::]:" + std::to_string(selected_port);
  LOG(INFO) << "Starting gRPC server on " << addr;
  grpc::ServerBuilder builder;
  builder.AddListeningPort(addr, grpc::InsecureServerCredentials(), &selected_port);
  builder.SetMaxReceiveMessageSize(10000000);
  builder.RegisterService(service.get());
  std::unique_ptr<grpc::Server> server = builder.BuildAndStart();
  if (!server) {
    LOG(ERROR) << "failed to create gRPC server";
    return 1;
  }
  LOG(INFO) << "gRPC server started on port " << selected_port;

  // Wait.
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  return 0;
}
