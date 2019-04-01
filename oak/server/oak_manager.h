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

#include "asylo/client.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/util/logging.h"
#include "oak/proto/enclave.pb.h"
#include "oak/proto/manager.grpc.pb.h"

class OakManager final : public ::oak::Manager::Service {
 public:
  OakManager();

  ::grpc::Status CreateNode(::grpc::ServerContext* context, const ::oak::CreateNodeRequest* request,
                            ::oak::CreateNodeResponse* response) override;

 private:
  void InitializeEnclaveManager();

  void CreateEnclave(const std::string& node_id, const std::string& module);

  oak::InitializeOutput GetEnclaveOutput(const std::string& node_id);

  std::string NewNodeId();

  void DestroyEnclave(const std::string& node_id);

  asylo::EnclaveManager* enclave_manager_;
  std::unique_ptr<asylo::SimLoader> enclave_loader_;

  uint64_t node_id_;
};
