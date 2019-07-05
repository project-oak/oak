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

#include "oak/server/enclave_server.h"

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
#include "oak/server/module_invocation.h"
#include "oak/server/oak_node.h"

namespace oak {

EnclaveServer::EnclaveServer()
    : credentials_(asylo::EnclaveServerCredentials(asylo::BidirectionalNullCredentialsOptions())) {}

asylo::Status EnclaveServer::Initialize(const asylo::EnclaveConfig& config) {
  LOG(INFO) << "Initializing Oak Application";
  const InitializeInput& initialize_input_message = config.GetExtension(initialize_input);
  const ApplicationConfiguration& application_configuration =
      initialize_input_message.application_configuration();
  if (application_configuration.nodes_size() != 1) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only application configurations with 1 Node are currently supported");
  }
  if (application_configuration.channels_size() != 0) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only application configurations with 0 Channels are currently supported");
  }
  const Node& node_configuration = application_configuration.nodes(0);
  if (!node_configuration.has_web_assembly_node()) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT,
                         "Only WebAssembly Nodes are currently supported");
  }
  // TODO: Support creating multiple Nodes and Channels connecting them.
  const WebAssemblyNode& web_assembly_node = node_configuration.web_assembly_node();
  node_ = OakNode::Create(web_assembly_node.module_bytes());
  if (node_ == nullptr) {
    return asylo::Status(asylo::error::GoogleError::INVALID_ARGUMENT, "Failed to create Oak Node");
  }

  return InitializeServer();
}

asylo::Status EnclaveServer::Run(const asylo::EnclaveInput& input, asylo::EnclaveOutput* output) {
  GetServerAddress(output);
  return asylo::Status::OkStatus();
}

asylo::Status EnclaveServer::Finalize(const asylo::EnclaveFinal& enclave_final) {
  FinalizeServer();
  return asylo::Status::OkStatus();
}

asylo::Status EnclaveServer::InitializeServer() {
  // Ensure that the server is only created and initialized once.
  absl::MutexLock lock(&server_mutex_);
  if (server_) {
    return asylo::Status::OkStatus();
  }

  ASYLO_ASSIGN_OR_RETURN(server_, CreateServer());

  // Start a new thread to process the gRPC completion queue.
  std::thread thread(&EnclaveServer::CompletionQueueLoop, this);
  thread.detach();

  return asylo::Status::OkStatus();
}

asylo::StatusOr<std::unique_ptr<grpc::Server>> EnclaveServer::CreateServer() {
  grpc::ServerBuilder builder;
  // Uses ":0" notation so that server listens on a free port.
  builder.AddListeningPort("[::]:0", credentials_, &port_);
  builder.RegisterService(node_.get());

  // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak
  // Node.
  completion_queue_ = builder.AddCompletionQueue();
  builder.RegisterAsyncGenericService(&module_service_);

  std::unique_ptr<grpc::Server> server = builder.BuildAndStart();
  if (!server) {
    return asylo::Status(asylo::error::GoogleError::INTERNAL, "Failed to start gRPC server");
  }

  LOG(INFO) << "gRPC server is listening on port: " << port_;

  return std::move(server);
}

void EnclaveServer::GetServerAddress(asylo::EnclaveOutput* output) {
  oak::InitializeOutput* initialize_output = output->MutableExtension(oak::initialize_output);
  initialize_output->set_grpc_port(port_);
}

void EnclaveServer::FinalizeServer() {
  absl::MutexLock lock(&server_mutex_);
  if (server_) {
    LOG(INFO) << "Shutting down...";
    server_->Shutdown();
    server_ = nullptr;
  }
}

void EnclaveServer::CompletionQueueLoop() {
  LOG(INFO) << "Starting gRPC completion queue loop";
  // The stream object will delete itself when finished with the request,
  // after creating a new stream object for the next request.
  auto* stream = new ModuleInvocation(&module_service_, completion_queue_.get(), node_.get());
  stream->Start();
  while (true) {
    bool ok;
    void* tag;
    if (!completion_queue_->Next(&tag, &ok)) {
      LOG(FATAL) << "Failure reading from completion queue";
      return;
    }
    auto* callback = static_cast<std::function<void(bool)>*>(tag);
    (*callback)(ok);
    delete callback;
  }
}

}  // namespace oak
