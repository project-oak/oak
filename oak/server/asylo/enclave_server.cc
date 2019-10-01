/*
 * Copyright 2019 The Project Oak Authors
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

#include "enclave_server.h"

#include <functional>
#include <memory>
#include <string>
#include <thread>

#include "absl/synchronization/mutex.h"
#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/trusted_application.h"
#include "asylo/util/logging.h"
#include "asylo/util/status.h"
#include "asylo/util/status_macros.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"
#include "oak/proto/enclave.pb.h"
#include "oak/server/oak_runtime.h"

namespace oak {

EnclaveServer::EnclaveServer() : runtime_(absl::make_unique<OakRuntime>()) {}

asylo::Status EnclaveServer::Initialize(const asylo::EnclaveConfig& config) {
  LOG(INFO) << "Initializing Enclave Server";
  const InitializeInput& initialize_input_message = config.GetExtension(initialize_input);
  const ApplicationConfiguration& application_configuration =
      initialize_input_message.application_configuration();
  runtime_->Initialize(application_configuration);

  runtime_->Start();

  return asylo::Status::OkStatus();
}

asylo::Status EnclaveServer::Run(const asylo::EnclaveInput& input, asylo::EnclaveOutput* output) {
  oak::InitializeOutput* initialize_output = output->MutableExtension(oak::initialize_output);
  initialize_output->set_grpc_port(runtime_->GetPort());
  return asylo::Status::OkStatus();
}

asylo::Status EnclaveServer::Finalize(const asylo::EnclaveFinal& enclave_final) {
  runtime_->Stop();
  return asylo::Status::OkStatus();
}

}  // namespace oak
