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

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/util/logging.h"
#include "dev_oak_loader.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"

ABSL_FLAG(std::string, config, "", "Application configuration file");

void sigint_handler(int) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // We install an explicit SIGINT handler, as for some reason the default one
  // does not seem to work.
  std::signal(SIGINT, sigint_handler);

  // Create loader instance.
  std::unique_ptr<oak::DevOakLoader> loader = absl::make_unique<oak::DevOakLoader>();

  // Load application configuration.
  std::unique_ptr<oak::ApplicationConfiguration> application_config =
      oak::ReadConfigFromFile(absl::GetFlag(FLAGS_config));

  asylo::StatusOr<oak::CreateApplicationResponse> result =
      loader->CreateApplication(*application_config);
  if (!result.ok()) {
    LOG(QFATAL) << "Failed to create application";
    return 1;
  }
  oak::CreateApplicationResponse response = result.ValueOrDie();
  std::stringstream address;
  address << "0.0.0.0:" << response.grpc_port();
  std::string application_id(response.application_id());
  LOG(INFO) << "Oak Application id=" << application_id << ": " << address.str();

  // Wait.
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  return 0;
}
