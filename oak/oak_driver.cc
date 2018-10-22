/*
 *
 * Copyright 2018 Asylo authors
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
 *
 */

#include "absl/strings/str_split.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/client.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"

#include "asylo/grpc/util/enclave_server.pb.h"
#include "oak/oak.pb.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

DEFINE_string(enclave_path, "", "Path to enclave to load");

DEFINE_string(expressions, "", "A comma-separated list of expressions to pass to the enclave");
DEFINE_string(wasm_module, "", "A wasm module to load");

int main(int argc, char *argv[]) {
  // Setup.
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  // Validate flags.
  if (FLAGS_expressions.empty()) {
    LOG(QFATAL) << "Must supply a non-empty list of expressions with --expressions";
  }

  std::vector<std::string> expressions = absl::StrSplit(FLAGS_expressions, ',');

  // Initialise enclave.
  asylo::EnclaveManager::Configure(asylo::EnclaveManagerOptions());
  auto manager_result = asylo::EnclaveManager::Instance();
  if (!manager_result.ok()) {
    LOG(QFATAL) << "EnclaveManager unavailable: " << manager_result.status();
  }
  asylo::EnclaveManager *manager = manager_result.ValueOrDie();
  std::cout << "Loading " << FLAGS_enclave_path << std::endl;
  asylo::SimLoader loader(FLAGS_enclave_path, /*debug=*/true);

  asylo::EnclaveConfig config;
  asylo::ServerConfig *server_config = config.MutableExtension(asylo::server_input_config);
  server_config->set_host("0.0.0.0");
  server_config->set_port(8888);
  asylo::Status status = manager->LoadEnclave("oak_enclave", loader, config);
  if (!status.ok()) {
    LOG(QFATAL) << "Load " << FLAGS_enclave_path << " failed: " << status;
  }
  LOG(INFO) << "Enclave initialised";

  asylo::EnclaveClient *client = manager->GetClient("oak_enclave");

  // Program enclave with initial script.
  {
    LOG(INFO) << "Programming enclave";

    // Read wasm module into a string.
    std::ifstream t(FLAGS_wasm_module, std::ifstream::in);
    std::stringstream buffer;
    buffer << t.rdbuf();

    LOG(INFO) << "Loaded module: " << buffer.str();

    asylo::EnclaveInput input;
    input.MutableExtension(oak::initialise_input)->set_wasm_module(buffer.str());
    asylo::EnclaveOutput output;
    status = client->EnterAndRun(input, &output);
    if (!status.ok()) {
      LOG(QFATAL) << "EnterAndRun failed: " << status;
    }
    LOG(INFO) << "Enclave programmed";
  }

  // Evaluate expressions in the enclave.
  for (const auto &expression : expressions) {
    LOG(INFO) << "sending expression to enclave: " << expression;
    asylo::EnclaveInput input;
    input.MutableExtension(oak::evaluate_input)->set_input_data(expression);
    asylo::EnclaveOutput output;
    status = client->EnterAndRun(input, &output);
    if (!status.ok()) {
      LOG(QFATAL) << "EnterAndRun failed: " << status;
    }

    std::cout << "Message from enclave: " << output.GetExtension(oak::evaluate_output).output_data()
              << std::endl;
  }

  // Wait.
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Seconds(30));

  // Finalization

  LOG(INFO) << "Destroying enclave";
  asylo::EnclaveFinal final_input;
  status = manager->DestroyEnclave(client, final_input);
  if (!status.ok()) {
    LOG(QFATAL) << "Destroy " << FLAGS_enclave_path << " failed: " << status;
  }
  LOG(INFO) << "Enclave destroyed";

  return 0;
}
