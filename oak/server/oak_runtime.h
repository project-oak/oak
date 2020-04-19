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

#ifndef OAK_SERVER_OAK_RUNTIME_H_
#define OAK_SERVER_OAK_RUNTIME_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/synchronization/mutex.h"
#include "include/grpcpp/security/server_credentials.h"
#include "include/grpcpp/server.h"
#include "oak/proto/application.pb.h"
#include "oak/proto/oak_abi.pb.h"
#include "oak/server/oak_grpc_node.h"
#include "oak/server/oak_node.h"

namespace oak {

// OakRuntime contains the common C++ parts of a runtime needed for an Oak
// System, but mostly acts as a proxy for the Rust runtime.
class OakRuntime {
 public:
  static std::unique_ptr<OakRuntime> Create(
      const application::ApplicationConfiguration& config,
      std::shared_ptr<grpc::ServerCredentials> grpc_credentials);
  ~OakRuntime() = default;

  void Start() const;
  void Stop() const;

  void CreateAndRunPseudoNode(const std::string& config_name, NodeId node_id, Handle handle) const;

 private:
  OakRuntime(const application::ApplicationConfiguration& config,
             std::shared_ptr<grpc::ServerCredentials> grpc_credentials);
  OakRuntime& operator=(const OakRuntime& other) = delete;

  std::unique_ptr<OakNode> CreateNode(const std::string& config_name, NodeId node_id) const;

  // Information derived from ApplicationConfiguration, const after construction:

  // Config names that refer to a storage proxy node.
  std::map<std::string, std::unique_ptr<std::string>> storage_config_;
  // Config names that refer to a gRPC client node.
  std::map<std::string, std::unique_ptr<std::string>> grpc_client_config_;
  // Config names that refer to a Roughtime client node.
  std::map<std::string, std::unique_ptr<application::RoughtimeClientConfiguration>>
      roughtime_client_config_;

  // gRPC pseudo-node.
  std::unique_ptr<OakGrpcNode> grpc_node_;
  // Handle for the write half of the gRPC server notification channel, relative
  // to the gRPC server pseudo-Node
  Handle grpc_handle_;
};  // class OakRuntime

}  // namespace oak

#endif  // OAK_SERVER_OAK_RUNTIME_H_
