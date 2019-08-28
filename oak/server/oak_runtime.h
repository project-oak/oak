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

#ifndef OAK_SERVER_RUNTIME_H_
#define OAK_SERVER_RUNTIME_H_

#include <memory>
#include <string>

#include "asylo/util/status.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "oak/proto/enclave.pb.h"
#include "oak/proto/oak_api.pb.h"
#include "oak/server/oak_node.h"

namespace oak {
// OakRuntime contains the common runtime needed for an Oak System. The Runtime is responsible for
// Initializing and Running a gRPC server, creating the nodes and channels and keeping track of the
// connectivity.
// For now, it only supports one node.
//
// It can run in its own enclave, but this is optional. See /asylo/ for how to use it with an
// enclave

class OakRuntime {
 public:
  OakRuntime(){};

  virtual ~OakRuntime() = default;

  // Initializes a gRPC server. If the server is already initialized, does nothing.
  asylo::Status InitializeServer(const ApplicationConfiguration& config,
                                 const std::shared_ptr<grpc::ServerCredentials> credentials);
  // Gets the address of the hosted gRPC server and writes it to server_output_config
  // extension of |output|.
  int GetServerAddress();

  // Finalizes the gRPC server by calling ::gprc::Server::Shutdown().
  void FinalizeServer();

 private:
  // Creates a gRPC server that hosts node_ on a free port with credentials_.
  asylo::StatusOr<std::unique_ptr<::grpc::Server>> CreateServer(
      const std::shared_ptr<grpc::ServerCredentials> credentials);

  void SetUpChannels();

  // Consumes gRPC events from the completion queue in an infinite loop.
  void CompletionQueueLoop();

  // The gRPC server.
  std::unique_ptr<::grpc::Server> server_;

  // The port on which the server is listening.
  int port_;

  std::unique_ptr<OakNode> node_;
  grpc::AsyncGenericService module_service_;
  std::unique_ptr<grpc::ServerCompletionQueue> completion_queue_;
};  // namespace oak

}  // namespace oak

#endif  // OAK_SERVER_RUNTIME_H_
