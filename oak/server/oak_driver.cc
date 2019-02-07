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

#include "absl/strings/str_split.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "asylo/client.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/util/logging.h"
#include "gflags/gflags.h"

#include "oak/proto/oak.pb.h"
#include "oak/proto/scheduling_service.grpc.pb.h"

#include <csignal>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

DEFINE_string(enclave_path, "", "Path to enclave to load");

class OakService final : public ::oak::SchedulingService::Service {
  ::grpc::Status Create(::grpc::ServerContext *context, const ::oak::CreateRequest *request,
                        ::oak::CreateResponse *response) {
    // TODO: Implement this method.
    // The logic currently in the main method of this file must really live inside this gRPC
    // service, so that enclaves can be created on demand by calling the Scheduling Service.
    return ::grpc::Status::OK;
  }
};

void sigint_handler(int param) {
  LOG(QFATAL) << "SIGINT received";
  exit(1);
}

int main(int argc, char *argv[]) {
  // Setup.
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  // We install an explicit SIGINT handler, as for some reason the default one does not seem to
  // work.
  std::signal(SIGINT, sigint_handler);

  // Initialize enclave.
  asylo::EnclaveManager::Configure(asylo::EnclaveManagerOptions());
  auto manager_result = asylo::EnclaveManager::Instance();
  if (!manager_result.ok()) {
    LOG(QFATAL) << "EnclaveManager unavailable: " << manager_result.status();
  }
  asylo::EnclaveManager *manager = manager_result.ValueOrDie();
  std::cout << "Loading " << FLAGS_enclave_path << std::endl;
  asylo::SimLoader loader(FLAGS_enclave_path, /*debug=*/true);

  // Loading.
  {
    asylo::EnclaveConfig config;
    oak::InitializeInput *initialize_input = config.MutableExtension(oak::initialize_input);
    // TODO: Load Oak Module and pass it to the enclave.
    initialize_input->set_module("TODO");
    asylo::Status status = manager->LoadEnclave("oak_enclave", loader, config);
    if (!status.ok()) {
      LOG(QFATAL) << "Load " << FLAGS_enclave_path << " failed: " << status;
    }
  }

  asylo::EnclaveClient *client = manager->GetClient("oak_enclave");

  // Initialisation.
  // This does not actually do anything interesting at the moment.
  {
    LOG(INFO) << "Initializing enclave";
    asylo::EnclaveInput input;
    asylo::EnclaveOutput output;
    asylo::Status status = client->EnterAndRun(input, &output);
    if (!status.ok()) {
      LOG(QFATAL) << "EnterAndRun failed: " << status;
    }
    LOG(INFO) << "Enclave initialized";
  }

  // Wait.
  {
    absl::Notification server_timeout;
    server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));
  }

  // Finalisation.
  {
    LOG(INFO) << "Destroying enclave";
    asylo::EnclaveFinal final_input;
    asylo::Status status = manager->DestroyEnclave(client, final_input);
    if (!status.ok()) {
      LOG(QFATAL) << "Destroy " << FLAGS_enclave_path << " failed: " << status;
    }
    LOG(INFO) << "Enclave destroyed";
  }

  return 0;
}
