/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/common/app_config.h"
#include "oak/common/utils.h"

#include <csignal>
#include <memory>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "asylo/util/logging.h"

ABSL_FLAG(std::string, module, "", "File containing the compiled WebAssembly module");
ABSL_FLAG(bool, logging, false, "Enable application logging");
ABSL_FLAG(std::string, storage_address, "127.0.0.1:7867",
          "Address ot the storage provider to connect to");
ABSL_FLAG(int, grpc_port, 8080, "Port for the Application to listen on");
ABSL_FLAG(std::string, output_file, "", "File to write an application configuration to");

void sigint_handler(int) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // We install an explicit SIGINT handler, as for some reason the default one
  // does not seem to work.
  std::signal(SIGINT, sigint_handler);

  // Create an application configuration.
  std::string module_bytes = oak::utils::read_file(absl::GetFlag(FLAGS_module));
  auto application_config = oak::DefaultConfig(module_bytes);

  // Set application configuration parameters.
  if (absl::GetFlag(FLAGS_logging)) {
    oak::AddLoggingToConfig(application_config.get());
  }
  oak::AddStorageToConfig(application_config.get(), absl::GetFlag(FLAGS_storage_address));
  oak::AddGrpcPortToConfig(application_config.get(), absl::GetFlag(FLAGS_grpc_port));

  std::string output_file = absl::GetFlag(FLAGS_output_file);
  if (output_file.empty()) {
    LOG(QFATAL) << "Output file is not specified";
    return 1;
  }
  oak::WriteConfigToFile(application_config.get(), output_file);

  return 0;
}
