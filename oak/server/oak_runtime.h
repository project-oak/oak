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
#include <vector>

#include "asylo/util/status.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "oak/proto/manager.pb.h"
#include "oak/proto/oak_api.pb.h"
#include "oak/server/logging_node.h"
#include "oak/server/oak_grpc_node.h"
#include "oak/server/oak_node.h"
#include "oak/server/storage/storage_node.h"

namespace oak {
// OakRuntime contains the common runtime needed for an Oak System. The Runtime is responsible for
// Initializing and Running a gRPC server, creating the nodes and channels and keeping track of
// the connectivity. For now, it only supports one node.
//
// It can run in its own enclave, but this is optional. See /asylo/ for how to use it with an
// enclave

class OakRuntime {
 public:
  OakRuntime() = default;
  virtual ~OakRuntime() = default;

  // Initializes a gRPC server. If the server is already initialized, does nothing.
  asylo::Status Initialize(const ApplicationConfiguration& config);
  asylo::Status Start();
  asylo::Status Stop();

  int32_t GetPort();

 private:
  // Collection of Wasm nodes indexed by node name.
  std::map<std::string, std::unique_ptr<OakNode> > wasm_nodes_;

  // TODO: These are hardcoded now. Make them generic nodes and channels and use config.
  // Pseudo-nodes.
  std::unique_ptr<OakGrpcNode> grpc_node_;
  std::unique_ptr<LoggingNode> logging_node_;
  std::unique_ptr<StorageNode> storage_node_;
};  // class OakRuntime

}  // namespace oak

#endif  // OAK_SERVER_RUNTIME_H_
