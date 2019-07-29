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

#include <string>

#include "absl/strings/string_view.h"
#include "asylo/client.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/util/logging.h"
#include "oak/proto/enclave.pb.h"
#include "oak/proto/manager.grpc.pb.h"

namespace oak {

class OakManager final : public Manager::Service {
 public:
  explicit OakManager(absl::string_view enclave_path);

  grpc::Status CreateApplication(grpc::ServerContext* context,
                                 const CreateApplicationRequest* request,
                                 CreateApplicationResponse* response) override;

 private:
  void InitializeEnclaveManager();

  grpc::Status CreateEnclave(const std::string& application_id,
                             const oak::ApplicationConfiguration& application_configuration);

  asylo::StatusOr<InitializeOutput> GetEnclaveOutput(const std::string& application_id);

  std::string NewApplicationId();

  void DestroyEnclave(const std::string& node_id);

  asylo::EnclaveManager* enclave_manager_;
  std::unique_ptr<asylo::SimLoader> enclave_loader_;
  std::string enclave_path_;

  uint64_t application_id_;
};

}  // namespace oak
