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

#ifndef OAK_SERVER_OAK_NODE_H_
#define OAK_SERVER_OAK_NODE_H_

#include <memory>
#include <thread>
#include <unordered_map>

#include "absl/base/thread_annotations.h"
#include "absl/types/span.h"
#include "oak/common/handles.h"
#include "oak/proto/application.grpc.pb.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/server/channel.h"
#include "oak/storage/storage_manager.h"
#include "src/interp/interp.h"

namespace oak {

typedef std::unordered_map<Handle, std::unique_ptr<ChannelHalf>> ChannelHalfTable;

class OakNode final : public Application::Service {
 public:
  // Creates an Oak node by loading the Wasm module code.
  static std::unique_ptr<OakNode> Create(const std::string& module);

  // Performs an Oak Module gRPC invocation. Takes ownership of the passed in request data.
  void ProcessModuleInvocation(grpc::GenericServerContext* context,
                               std::unique_ptr<Message> request_data);

  // Returns the next response from a gRPC invocation.
  oak::GrpcResponse NextResponse();

 private:
  // Clients should construct OakNode instances with Create() (which
  // can fail).
  OakNode();

  grpc::Status GetAttestation(grpc::ServerContext* context, const GetAttestationRequest* request,
                              GetAttestationResponse* response) override;

  void InitEnvironment(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_read` host function.
  wabt::interp::HostFunc::Callback OakChannelRead(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_write` host function.
  wabt::interp::HostFunc::Callback OakChannelWrite(wabt::interp::Environment* env);

  // Native implementation of the `oak.wait_on_channels` host function.
  wabt::interp::HostFunc::Callback OakWaitOnChannels(wabt::interp::Environment* env);

  wabt::interp::Environment env_;
  // TODO: Use smart pointers.
  wabt::interp::DefinedModule* module_;

  // Hold the mapping between per-Node channel handles and channel half instances
  ChannelHalfTable channel_halves_;

  // Hold on to the other halves of channels that the node uses to perform gRPC.
  std::unique_ptr<MessageChannelWriteHalf> name_half_;
  std::unique_ptr<MessageChannelWriteHalf> req_half_;
  std::unique_ptr<MessageChannelReadHalf> rsp_half_;

  StorageManager storage_manager_;
  std::unique_ptr<Storage::Stub> storage_service_;
};

}  // namespace oak

#endif  // OAK_SERVER_OAK_NODE_H_
