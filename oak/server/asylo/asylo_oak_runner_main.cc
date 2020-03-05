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

#include "absl/debugging/stacktrace.h"
#include "absl/debugging/symbolize.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/util/logging.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/common/app_config.h"
#include "oak/common/utils.h"
#include "oak/proto/application.grpc.pb.h"
#include "oak/server/asylo/asylo_oak_loader.h"

ABSL_FLAG(std::string, application, "", "Application configuration file");
ABSL_FLAG(std::string, enclave_path, "", "Path of the enclave to load");
ABSL_FLAG(bool, debug, true, "Run in debug mode");

void sigint_handler(int param) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

void crash_handler(int param) {
  constexpr int kMaxStackDepth = 20;
  void* result[kMaxStackDepth];
  int depth = absl::GetStackTrace(result, kMaxStackDepth, 1);
  for (int i = 0; i < depth; i++) {
    char tmp[1024];
    const char* symbol = "(unknown)";
    if (absl::Symbolize(result[i], tmp, sizeof(tmp))) {
      symbol = tmp;
    }
    LOG(ERROR) << "backtrace[" << i << "] = " << result[i] << " " << symbol;
  }
  LOG(QFATAL) << "Process crashed, signal " << param;
}

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  if (absl::GetFlag(FLAGS_debug)) {
#if defined(NDEBUG)
    LOG(ERROR) << "Debug mode not available in non-debug build!";
#else
    absl::InitializeSymbolizer(argv[0]);
    std::signal(SIGILL, crash_handler);
    std::signal(SIGBUS, crash_handler);
    std::signal(SIGSEGV, crash_handler);
#endif
  }

  // We install an explicit SIGINT handler, as for some reason the default one
  // does not seem to work.
  std::signal(SIGINT, sigint_handler);

  // Create loader instance.
  std::unique_ptr<oak::AsyloOakLoader> loader =
      absl::make_unique<oak::AsyloOakLoader>(absl::GetFlag(FLAGS_enclave_path));

  // Load application configuration.
  std::unique_ptr<oak::ApplicationConfiguration> application_config =
      oak::ReadConfigFromFile(absl::GetFlag(FLAGS_application));

  asylo::Status status = loader->CreateApplication(*application_config);
  if (!status.ok()) {
    LOG(ERROR) << "Failed to create application";
    return 1;
  }
  std::stringstream address;
  address << "0.0.0.0:" << application_config->grpc_port();
  LOG(INFO) << "Oak Application: " << address.str();

  // Wait (same as `sleep(86400)`).
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  loader->TerminateApplication();

  return 0;
}
