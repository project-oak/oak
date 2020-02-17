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

#include "oak/server/asylo/asylo_oak_loader.h"
#include "absl/memory/memory.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/enclave_assertion_authority_config.pb.h"
#include "asylo/util/logging.h"
#include "asylo/util/statusor.h"

namespace oak {

AsyloOakLoader::AsyloOakLoader(absl::string_view enclave_path) : enclave_path_(enclave_path) {
  InitializeEnclaveManager();
}

asylo::Status AsyloOakLoader::CreateApplication(
    const oak::ApplicationConfiguration& application_configuration) {
  LOG(INFO) << "Creating an Oak application";

  asylo::Status status = CreateEnclave(application_configuration);
  if (!status.ok()) {
    return status;
  }

  asylo::StatusOr<oak::InitializeOutput> result = GetEnclaveOutput();
  return result.status();
}

asylo::Status AsyloOakLoader::TerminateApplication() {
  LOG(INFO) << "Terminating an Oak application";

  DestroyEnclave();
  return asylo::Status::OkStatus();
}

void AsyloOakLoader::InitializeEnclaveManager() {
  LOG(INFO) << "Initializing enclave manager";
  asylo::EnclaveManager::Configure(asylo::EnclaveManagerOptions());
  auto manager_result = asylo::EnclaveManager::Instance();
  if (!manager_result.ok()) {
    LOG(QFATAL) << "Could not initialize enclave manager: " << manager_result.status();
  }
  enclave_manager_ = manager_result.ValueOrDie();
  LOG(INFO) << "Enclave manager initialized";
  LOG(INFO) << "Loading enclave code from " << enclave_path_;
  enclave_loader_ = absl::make_unique<asylo::SgxLoader>(enclave_path_,
                                                        /*debug=*/true);
}

asylo::Status AsyloOakLoader::CreateEnclave(
    const oak::ApplicationConfiguration& application_configuration) {
  LOG(INFO) << "Creating enclave";
  asylo::EnclaveConfig config;
  // Explicitly initialize the null assertion authority in the enclave.
  asylo::EnclaveAssertionAuthorityConfig* authority_config =
      config.add_enclave_assertion_authority_configs();
  asylo::SetNullAssertionDescription(authority_config->mutable_description());
  oak::InitializeInput* initialize_input = config.MutableExtension(oak::initialize_input);
  *initialize_input->mutable_application_configuration() = application_configuration;
  asylo::Status status = enclave_manager_->LoadEnclave(enclave_name_, *enclave_loader_, config);
  if (!status.ok()) {
    LOG(ERROR) << "Could not load enclave " << enclave_path_ << ": " << status;
  } else {
    LOG(INFO) << "Enclave created";
  }
  return status;
}

asylo::StatusOr<oak::InitializeOutput> AsyloOakLoader::GetEnclaveOutput() {
  LOG(INFO) << "Initializing enclave";
  asylo::EnclaveClient* client = enclave_manager_->GetClient(enclave_name_);
  asylo::EnclaveInput input;
  asylo::EnclaveOutput output;
  asylo::Status status = client->EnterAndRun(input, &output);
  if (!status.ok()) {
    LOG(ERROR) << "EnterAndRun failed: " << status;
    return status;
  }
  LOG(INFO) << "Enclave initialized";
  return output.GetExtension(oak::initialize_output);
}

void AsyloOakLoader::DestroyEnclave() {
  LOG(INFO) << "Destroying enclave";
  asylo::EnclaveClient* client = enclave_manager_->GetClient(enclave_name_);
  asylo::EnclaveFinal final_input;
  asylo::Status status = enclave_manager_->DestroyEnclave(client, final_input);
  if (!status.ok()) {
    LOG(QFATAL) << "Destroy " << enclave_path_ << " failed: " << status;
  }
  LOG(INFO) << "Enclave destroyed";
}

}  // namespace oak
