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

#include <sstream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "oak/common/logging.h"
#include "oak/server/dev/dev_oak_loader.h"

ABSL_FLAG(std::string, application, "", "Application configuration file");

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // Create loader instance.
  std::unique_ptr<oak::DevOakLoader> loader = absl::make_unique<oak::DevOakLoader>();

  // Load application configuration.
  std::unique_ptr<oak::ApplicationConfiguration> application_config =
      oak::ReadConfigFromFile(absl::GetFlag(FLAGS_application));

  grpc::Status status = loader->CreateApplication(*application_config);
  if (!status.ok()) {
    OAK_LOG(ERROR) << "Failed to create application";
    return 1;
  }
  std::stringstream address;
  address << "0.0.0.0:" << application_config->grpc_port();
  OAK_LOG(INFO) << "Oak Application: " << address.str();

  // Wait (same as `sleep(86400)`).
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  loader->TerminateApplication();

  return 0;
}
