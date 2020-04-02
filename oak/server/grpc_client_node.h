/*
 * Copyright 2020 The Project Oak Authors
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

#ifndef OAK_SERVER_GRPC_CLIENT_NODE_H_
#define OAK_SERVER_GRPC_CLIENT_NODE_H_

#include <memory>
#include <string>

#include "grpcpp/generic/generic_stub.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/common/handles.h"
#include "oak/server/oak_node.h"

namespace oak {

class GrpcClientNode final : public OakNode {
 public:
  GrpcClientNode(const std::string& name, NodeId node_id, const std::string& grpc_address);

 private:
  bool HandleInvocation(Handle invocation_handle);
  void FailInvocation(Handle rsp_handle, grpc::Status status);
  void Run(Handle handle) override;

  std::shared_ptr<grpc::ChannelInterface> channel_;
  std::unique_ptr<grpc::GenericStub> stub_;
};

}  // namespace oak

#endif  // OAK_SERVER_GRPC_CLIENT_NODE_H_
