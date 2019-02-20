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
#include <thread>

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
  EnclaveServer()
      : node_(nullptr),
        credentials_(
            ::asylo::EnclaveServerCredentials(::asylo::BidirectionalNullCredentialsOptions())),
        completion_queue_(nullptr){};

  ~EnclaveServer() = default;

  asylo::Status Initialize(const asylo::EnclaveConfig &config) override {
    LOG(INFO) << "Initializing Oak Instance";
    const oak::InitializeInput &initialize_input = config.GetExtension(oak::initialize_input);
    node_ = absl::make_unique<oak::grpc_server::OakNode>(initialize_input.node_id(),
                                                         initialize_input.module());
    return InitializeServer();
  }

  asylo::Status Run(const asylo::EnclaveInput &input, asylo::EnclaveOutput *output) override {
    GetServerAddress(output);
    return asylo::Status::OkStatus();
  }

  asylo::Status Finalize(const asylo::EnclaveFinal &enclave_final) override {
    FinalizeServer();
    return asylo::Status::OkStatus();
  }

 private:
  // Initializes a gRPC server. If the server is already initialized, does nothing.
  asylo::Status InitializeServer() LOCKS_EXCLUDED(server_mutex_) {
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

  // Creates a gRPC server that hosts node_ on a free port with credentials_.
  asylo::StatusOr<std::unique_ptr<::grpc::Server>> CreateServer()
      EXCLUSIVE_LOCKS_REQUIRED(server_mutex_) {
    ::grpc::ServerBuilder builder;
    // TODO: Listen on a free port (using ":0" notation).
    builder.AddListeningPort("[::]:30000", credentials_, &port_);
    builder.RegisterService(node_.get());

    // Add a completion queue and a generic service, in order to proxy incoming RPCs to the Oak
    // Node.
    completion_queue_ = builder.AddCompletionQueue();
    builder.RegisterAsyncGenericService(&generic_service_);

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

  // Creates a new gRPC event tag based on a number. gRPC tags are usually employed to uniquely
  // identify events, but we do not need to keep track of them, and therefore we just create them
  // based on arbitrary numbers.
  // See https://grpc.io/grpc/cpp/classgrpc_1_1_completion_queue.html.
  static void *tag(int i) { return reinterpret_cast<void *>(i); }

  // Processes the next available event from the completion queue, blocking if none is available.
  void ProcessNextEvent() {
    void *out_tag;
    bool ok = false;
    completion_queue_->Next(&out_tag, &ok);
    // TODO: Return the value of ok so that we can break the completion queue loop.
    if (!ok) {
      LOG(INFO) << "Could not process gRPC event from completion queue";
    }
  }

  // Consumes gRPC events from the completion queue in an infinite loop.
  void CompletionQueueLoop() {
    LOG(INFO) << "Starting gRPC completion queue loop";
    int i = 0;
    while (true) {
      ::grpc::GenericServerContext context;
      ::grpc::GenericServerAsyncReaderWriter stream(&context);

      // We request a new event corresponding to a generic call. This will create an entry in the
      // completion queue when a new call is available.
      generic_service_.RequestCall(&context, &stream, completion_queue_.get(),
                                   completion_queue_.get(), tag(i++));

      // Wait for a generic call to arrive.
      ProcessNextEvent();

      // Read request data.
      ::grpc::ByteBuffer request;
      stream.Read(&request, tag(i++));

      // Process the event related to the read we just requested.
      ProcessNextEvent();

      ::grpc::ByteBuffer response;

      // Invoke the actual gRPC handler on the Oak Node.
      ::grpc::Status status = node_->HandleGrpcCall(&context, &request, &response);
      if (!status.ok()) {
        LOG(INFO) << "Failed: " << status.error_message();
      }

      ::grpc::WriteOptions options;

      // Write response data.
      stream.WriteAndFinish(response, options, status, tag(i++));

      // Process the event related to the write we just requested.
      ProcessNextEvent();
    }
  }

  // Guards state related to the gRPC server (|server_| and |port_|).
  absl::Mutex server_mutex_;

  // The gRPC server.
  std::unique_ptr<::grpc::Server> server_ GUARDED_BY(server_mutex_);

  // The port on which the server is listening.
  int port_;

  std::unique_ptr<::oak::grpc_server::OakNode> node_;
  std::shared_ptr<::grpc::ServerCredentials> credentials_;

  ::grpc::AsyncGenericService generic_service_;
  std::unique_ptr<::grpc::ServerCompletionQueue> completion_queue_;
};

}  // namespace oak

#endif  // OAK_SERVER_ENCLAVE_SERVER_H_
