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
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/common/app_config.h"
#include "oak/proto/manager.grpc.pb.h"
#include "oak/server/asylo/asylo_oak_manager.h"
#include "examples/utils/utils.h"

ABSL_FLAG(std::string, enclave_path, "", "Path of the enclave to load");
ABSL_FLAG(std::string, module, "", "File containing the compiled WebAssembly module");

ABSL_FLAG(std::string, storage_address, "127.0.0.1:7867",
          "Address ot the storage provider to connect to");


void sigint_handler(int param) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // We install an explicit SIGINT handler, as for some reason the default one
  // does not seem to work.
  std::signal(SIGINT, sigint_handler);

  // Create manager instance.
  std::unique_ptr<oak::AsyloOakManager> manager =
      absl::make_unique<oak::AsyloOakManager>(absl::GetFlag(FLAGS_enclave_path));

  // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string module_bytes = oak::utils::read_file(absl::GetFlag(FLAGS_module));

  std::unique_ptr<oak::ApplicationConfiguration> application_config = 
      oak::DefaultConfig(module_bytes);
  oak::AddLoggingToConfig(application_config.get());
  oak::AddStorageToConfig(application_config.get(), absl::GetFlag(FLAGS_storage_address));
  asylo::StatusOr<oak::CreateApplicationResponse> result = manager->CreateApplication(
      *application_config);
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
