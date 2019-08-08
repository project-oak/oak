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

#include "dev_oak_manager.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "grpcpp/support/status_code_enum.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {

DevOakManager::DevOakManager() : Service(), application_id_(0) {
  LOG(INFO) << "Creating OakManager";
}

grpc::Status DevOakManager::CreateApplication(grpc::ServerContext* context,
                                              const oak::CreateApplicationRequest* request,
                                              oak::CreateApplicationResponse* response) {
  std::string application_id = NewApplicationId();
  LOG(INFO) << "Creating app with with id: " << application_id;
  auto runtime = absl::make_unique<OakRuntime>();
  auto status = runtime->Initialize(request->application_configuration());
  if (!status.ok()) {
    return status.ToOtherStatus<grpc::Status>();
  }

  grpc::ServerBuilder builder;
  int port;

  // Uses ":0" notation so that server listens on a free port.
  builder.AddListeningPort("[::]:0", grpc::InsecureServerCredentials(), &port);
  builder.RegisterService(runtime->GetGrpcService());

  // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak Node.
  auto completion_queue = builder.AddCompletionQueue();

  // Register an async service
  auto module_service = absl::make_unique<grpc::AsyncGenericService>();
  builder.RegisterAsyncGenericService(module_service.get());

  auto server = builder.BuildAndStart();
  if (!server) {
    grpc::Status(grpc::INTERNAL, "Failed to start gRPC server");
  }

  // moves ownership of unique pointers
  runtime->StartCompletionQueue(std::move(module_service), std::move(completion_queue));

  runtimes[application_id] = std::move(runtime);
  servers[application_id] = std::move(server);

  LOG(INFO) << "gRPC server is listening on port: " << port;

  response->set_application_id(application_id);
  response->set_grpc_port(port);
  return grpc::Status::OK;
}

std::string DevOakManager::NewApplicationId() {
  // For dev purposes, just increment a value
  std::stringstream id_str;
  id_str << application_id_;
  application_id_ += 1;
  return id_str.str();
}
}  // namespace oak
