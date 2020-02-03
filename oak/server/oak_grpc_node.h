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

#ifndef OAK_SERVER_OAK_GRPC_NODE_H_
#define OAK_SERVER_OAK_GRPC_NODE_H_

#include <thread>

#include "absl/synchronization/mutex.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/common/app_config.h"
#include "oak/server/channel.h"
#include "oak/server/oak_node.h"

namespace oak {

class OakGrpcNode final : public OakNode {
 public:
  // Create an Oak node with the `name` and gRPC `port`.
  // If `port` equals 0, then gRPC port is assigned automatically.
  static std::unique_ptr<OakGrpcNode> Create(BaseRuntime* runtime, const std::string& name,
                                             const uint16_t port = 0);
  virtual ~OakGrpcNode(){};

  void Start() override;
  void Stop() override;

  int GetPort() { return port_; };

  int32_t NextStreamID() LOCKS_EXCLUDED(id_mu_) {
    absl::MutexLock lock(&id_mu_);
    return next_stream_id_++;
  }

 private:
  friend class ModuleInvocation;

  OakGrpcNode(BaseRuntime* runtime, const std::string& name)
      : OakNode(runtime, name), next_stream_id_(1) {}
  OakGrpcNode(const OakGrpcNode&) = delete;
  OakGrpcNode& operator=(const OakGrpcNode&) = delete;

  MessageChannelWriteHalf* BorrowWriteChannel() const {
    return OakNode::BorrowWriteChannel(SingleHandle());
  }

  // Consumes gRPC events from the completion queue in an infinite loop.
  void CompletionQueueLoop();

  int port_;

  std::unique_ptr<::grpc::Server> server_;

  // gRPC async service and completion queue.
  std::unique_ptr<grpc::AsyncGenericService> module_service_;
  // The queue expects to deal with void* tag values that are always function pointers to
  // void(bool) functions.
  std::thread queue_thread_;
  std::unique_ptr<grpc::ServerCompletionQueue> completion_queue_;

  absl::Mutex id_mu_;  // protects next_stream_id_
  int32_t next_stream_id_ GUARDED_BY(id_mu_);
};

}  // namespace oak

#endif  // OAK_SERVER_OAK_GRPC_NODE_H_
