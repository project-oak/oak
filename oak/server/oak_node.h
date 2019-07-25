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
#include <unordered_map>

#include "absl/base/thread_annotations.h"
#include "absl/types/span.h"
#include "oak/common/handles.h"
#include "oak/proto/application.grpc.pb.h"
#include "oak/server/channel.h"
#include "src/interp/interp.h"

namespace oak {

typedef std::unordered_map<Handle, std::unique_ptr<ChannelHalf>> ChannelHalfTable;

class OakNode final : public Application::Service {
 public:
  struct InvocationResult {
    grpc::Status status;
    std::unique_ptr<Message> data;
  };

  // Creates an Oak node by loading the Wasm module code.
  static std::unique_ptr<OakNode> Create(const std::string& module);

  // Performs an Oak Module invocation. Takes ownership of the passed in request data.
  InvocationResult ProcessModuleInvocation(grpc::GenericServerContext* context,
                                           std::unique_ptr<Message> request_data);

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

  wabt::interp::Environment env_;
  // TODO: Use smart pointers.
  wabt::interp::DefinedModule* module_;

  ChannelHalfTable channel_halves_;
};

// RAII class to add a mapping from a handle to a channel half for the duration of a scope.
class ChannelMapping {
 public:
  ChannelMapping(ChannelHalfTable* table, Handle handle, std::unique_ptr<ChannelHalf> half)
      : table_(table), handle_(handle) {
    (*table_)[handle_] = std::move(half);
  }
  ~ChannelMapping() { table_->erase(handle_); }

 private:
  ChannelHalfTable* table_;
  Handle handle_;
};

}  // namespace oak

#endif  // OAK_SERVER_OAK_NODE_H_
