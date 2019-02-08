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
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"

#include "oak/proto/enclave.pb.h"
#include "oak/proto/scheduler.grpc.pb.h"

#include <csignal>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

DEFINE_string(enclave_path, "", "Path to enclave to load");

// TODO: Move to separate file.
class OakScheduler final : public ::oak::Scheduler::Service {
 public:
  OakScheduler() : Service(), node_id_(0) { InitializeEnclaveManager(); }

  ::grpc::Status CreateNode(::grpc::ServerContext *context, const ::oak::CreateNodeRequest *request,
                            ::oak::CreateNodeResponse *response) override {
    std::string node_id = NewNodeId();
    CreateEnclave(node_id, request->module());
    oak::InitializeOutput out = GetEnclaveOutput(node_id);
    response->set_port(out.port());
    response->set_node_id(node_id);
    return ::grpc::Status::OK;
  }

 private:
  void InitializeEnclaveManager() {
    LOG(INFO) << "Initializing enclave manager";
    asylo::EnclaveManager::Configure(asylo::EnclaveManagerOptions());
    auto manager_result = asylo::EnclaveManager::Instance();
    if (!manager_result.ok()) {
      LOG(QFATAL) << "Could not initialize enclave manager: " << manager_result.status();
    }
    enclave_manager_ = manager_result.ValueOrDie();
    LOG(INFO) << "Enclave manager initialized";
    LOG(INFO) << "Loading enclave code from " << FLAGS_enclave_path;
    enclave_loader_ = absl::make_unique<asylo::SimLoader>(FLAGS_enclave_path, /*debug=*/true);
  }

  void CreateEnclave(const std::string &node_id, const std::string &module) {
    LOG(INFO) << "Creating enclave";
    asylo::EnclaveConfig config;
    oak::InitializeInput *initialize_input = config.MutableExtension(oak::initialize_input);
    initialize_input->set_node_id(node_id);
    initialize_input->set_module(module);
    asylo::Status status = enclave_manager_->LoadEnclave(node_id, *enclave_loader_, config);
    if (!status.ok()) {
      LOG(QFATAL) << "Could not load enclave " << FLAGS_enclave_path << ": " << status;
    }
    LOG(INFO) << "Enclave created";
  }

  oak::InitializeOutput GetEnclaveOutput(const std::string &node_id) {
    LOG(INFO) << "Initializing enclave";
    asylo::EnclaveClient *client = enclave_manager_->GetClient(node_id);
    asylo::EnclaveInput input;
    asylo::EnclaveOutput output;
    asylo::Status status = client->EnterAndRun(input, &output);
    if (!status.ok()) {
      LOG(QFATAL) << "EnterAndRun failed: " << status;
    }
    LOG(INFO) << "Enclave initialized";
    return output.GetExtension(oak::initialize_output);
  }

  std::string NewNodeId() {
    // TODO: Generate UUID.
    std::stringstream id_str;
    id_str << node_id_;
    node_id_ += 1;
    return id_str.str();
  }

  void DestroyEnclave(const std::string &node_id) {
    LOG(INFO) << "Destroying enclave";
    asylo::EnclaveClient *client = enclave_manager_->GetClient(node_id);
    asylo::EnclaveFinal final_input;
    asylo::Status status = enclave_manager_->DestroyEnclave(client, final_input);
    if (!status.ok()) {
      LOG(QFATAL) << "Destroy " << FLAGS_enclave_path << " failed: " << status;
    }
    LOG(INFO) << "Enclave destroyed";
  }

  asylo::EnclaveManager *enclave_manager_;
  std::unique_ptr<asylo::SimLoader> enclave_loader_;

  uint64_t node_id_;
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

  // Create scheduler instance.
  std::unique_ptr<OakScheduler> service = absl::make_unique<OakScheduler>();

  // Initialize and run gRPC server.
  LOG(INFO) << "Starting gRPC server";
  ::grpc::ServerBuilder builder;
  int selected_port;
  builder.AddListeningPort("[::]:8888", ::grpc::InsecureServerCredentials(), &selected_port);
  builder.RegisterService(service.get());
  std::unique_ptr<::grpc::Server> server = builder.BuildAndStart();
  LOG(INFO) << "gRPC server started on port " << selected_port;

  // Wait.
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  return 0;
}
