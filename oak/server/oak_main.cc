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

#include <csignal>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/server/oak_manager.h"

void sigint_handler(int param) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

int main(int argc, char* argv[]) {
  // Setup.
  google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  // We install an explicit SIGINT handler, as for some reason the default one
  // does not seem to work.
  std::signal(SIGINT, sigint_handler);

  // Create manager instance.
  std::unique_ptr<oak::OakManager> service = absl::make_unique<oak::OakManager>();

  // Initialize and run gRPC server.
  LOG(INFO) << "Starting gRPC server";
  grpc::ServerBuilder builder;
  int selected_port;
  builder.AddListeningPort("[::]:8888", grpc::InsecureServerCredentials(), &selected_port);
  builder.RegisterService(service.get());
  std::unique_ptr<grpc::Server> server = builder.BuildAndStart();
  LOG(INFO) << "gRPC server started on port " << selected_port;

  // Wait.
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  return 0;
}
