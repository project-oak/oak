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

#include "absl/strings/str_cat.h"
#include "absl/synchronization/mutex.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/trusted_application.h"
#include "asylo/util/logging.h"
#include "asylo/util/status.h"
#include "asylo/util/status_macros.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/impl/codegen/service_type.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "include/grpcpp/server_builder.h"

#include "oak/proto/oak.pb.h"

namespace oak {

// Enclave for hosting a gRPC service.
//
// The gRPC service and credentials are configurable in the constructor.
//
// The server is initialized and started during Initialize(). Users of this
// class are expected to set the server's host and port in the EnclaveConfig
// provided to EnclaveManager::LoadEnclave() when loading their enclave.
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
  EnclaveServer(std::unique_ptr<::grpc::Service> service,
                std::shared_ptr<::grpc::ServerCredentials> credentials)
      : service_{std::move(service)}, credentials_{credentials} {}

  ~EnclaveServer() = default;

  // From TrustedApplication.
  asylo::Status Initialize(const asylo::EnclaveConfig &config) {
    LOG(INFO) << "Initializing Oak Instance";
    const oak::InitializeInput &initialize_input = config.GetExtension(oak::initialize_input);
    // TODO: Load module from the incoming request.
    return InitializeServer();
  }

  asylo::Status Run(const asylo::EnclaveInput &input, asylo::EnclaveOutput *output) {
    GetServerAddress(output);
    return asylo::Status::OkStatus();
  }

  asylo::Status Finalize(const asylo::EnclaveFinal &enclave_final) {
    FinalizeServer();
    return asylo::Status::OkStatus();
  }

 private:
  // Initializes a gRPC server. If the server is already initialized, does
  // nothing.
  asylo::Status InitializeServer() LOCKS_EXCLUDED(server_mutex_) {
    // Ensure that the server is only created and initialized once.
    absl::MutexLock lock(&server_mutex_);
    if (server_) {
      return asylo::Status::OkStatus();
    }

    ASYLO_ASSIGN_OR_RETURN(server_, CreateServer());
    return asylo::Status::OkStatus();
  }

  // Creates a gRPC server that hosts service_ on a free port with credentials_.
  asylo::StatusOr<std::unique_ptr<::grpc::Server>> CreateServer()
      EXCLUSIVE_LOCKS_REQUIRED(server_mutex_) {
    ::grpc::ServerBuilder builder;
    // TODO: Listen on a free port (using ":0" notation).
    builder.AddListeningPort("0.0.0.0:8888", credentials_, &port_);
    builder.RegisterService(service_.get());
    std::unique_ptr<::grpc::Server> server = builder.BuildAndStart();
    if (!server) {
      return asylo::Status(asylo::error::GoogleError::INTERNAL, "Failed to start gRPC server");
    }

    LOG(INFO) << "gRPC server is listening on port :" << port_;

    return std::move(server);
  }

  // Gets the address of the hosted gRPC server and writes it to
  // server_output_config extension of |output|.
  void GetServerAddress(asylo::EnclaveOutput *output) EXCLUSIVE_LOCKS_REQUIRED(server_mutex_) {
    oak::InitializeOutput *initialize_output = output->MutableExtension(oak::initialize_output);
    initialize_output->set_port(port_);
  }

  // Finalizes the gRPC server by calling ::gprc::Server::Shutdown().
  void FinalizeServer() LOCKS_EXCLUDED(server_mutex_) {
    absl::MutexLock lock(&server_mutex_);
    if (server_) {
      LOG(INFO) << "Shutting down...";
      server_->Shutdown();
      server_ = nullptr;
    }
  }

  // Guards state related to the gRPC server (|server_| and |port_|).
  absl::Mutex server_mutex_;

  // A gRPC server hosting |messenger_|.
  std::unique_ptr<::grpc::Server> server_ GUARDED_BY(server_mutex_);

  // The port on which the server is listening.
  int port_;

  std::unique_ptr<::grpc::Service> service_;
  std::shared_ptr<::grpc::ServerCredentials> credentials_;
};

}  // namespace oak

#endif  // OAK_SERVER_ENCLAVE_SERVER_H_
