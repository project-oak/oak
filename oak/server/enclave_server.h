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

// This file is mostly copied from
// https://github.com/google/asylo/blob/master/asylo/grpc/util/enclave_server.h

#ifndef OAK_SERVER_ENCLAVE_SERVER_H_
#define OAK_SERVER_ENCLAVE_SERVER_H_

#include <memory>
#include <string>

#include "absl/synchronization/mutex.h"
#include "asylo/grpc/auth/enclave_server_credentials.h"
#include "asylo/grpc/auth/null_credentials_options.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/trusted_application.h"
#include "asylo/util/status.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/impl/codegen/service_type.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "oak/proto/enclave.pb.h"
#include "oak/server/oak_node.h"

namespace oak {

// Enclave for hosting an Oak Node.
//
// The Run() entry-point can be used to retrieve the server's host and port.
// The port may be different than the value provided at enclave initialization
// if the EnclaveConfig specified a port of 0 (indicates that the operating
// system should select an available port).
//
// The server is shut down during Finalize(). To ensure proper server shutdown,
// users of this class are expected to trigger enclave finalization by calling
// EnclaveManager::DestroyEnclave() at some point during lifetime of their
// application.
class EnclaveServer final : public asylo::TrustedApplication {
 public:
  EnclaveServer();

  ~EnclaveServer() = default;

  asylo::Status Initialize(const asylo::EnclaveConfig& config) override;

  asylo::Status Run(const asylo::EnclaveInput& input, asylo::EnclaveOutput* output) override;

  asylo::Status Finalize(const asylo::EnclaveFinal& enclave_final) override;

  // Initializes a gRPC server. If the server is already initialized, does nothing.
  asylo::Status InitializeServer() LOCKS_EXCLUDED(server_mutex_);

  // Creates a gRPC server that hosts node_ on a free port with credentials_.
  asylo::StatusOr<std::unique_ptr<::grpc::Server>> CreateServer()
      EXCLUSIVE_LOCKS_REQUIRED(server_mutex_);

  // Gets the address of the hosted gRPC server and writes it to server_output_config
  // extension of |output|.
  void GetServerAddress(asylo::EnclaveOutput* output) EXCLUSIVE_LOCKS_REQUIRED(server_mutex_);

  // Finalizes the gRPC server by calling ::gprc::Server::Shutdown().
  void FinalizeServer() LOCKS_EXCLUDED(server_mutex_);

  // Consumes gRPC events from the completion queue in an infinite loop.
  void CompletionQueueLoop();

  // Guards state related to the gRPC server (|server_| and |port_|).
  absl::Mutex server_mutex_;

  // The gRPC server.
  std::unique_ptr<::grpc::Server> server_ GUARDED_BY(server_mutex_);

  // The port on which the server is listening.
  int port_;

  std::unique_ptr<OakNode> node_;
  std::shared_ptr<grpc::ServerCredentials> credentials_;

  grpc::AsyncGenericService module_service_;
  std::unique_ptr<grpc::ServerCompletionQueue> completion_queue_;
};

}  // namespace oak

#endif  // OAK_SERVER_ENCLAVE_SERVER_H_
