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
#include "oak/proto/application.grpc.pb.h"
#include "oak/server/channel.h"
#include "src/interp/interp.h"

namespace oak {

using Handle = uint64_t;

// Keep in sync with /rust/oak/src/lib.rs.
const Handle LOGGING_CHANNEL_HANDLE = 1;
const Handle GRPC_METHOD_NAME_CHANNEL_HANDLE = 2;
const Handle GRPC_IN_CHANNEL_HANDLE = 3;
const Handle GRPC_OUT_CHANNEL_HANDLE = 4;

typedef std::unordered_map<Handle, std::unique_ptr<ChannelHalf>> ChannelHalfTable;

class OakNode final : public Application::Service {
 public:
  // Creates an Oak node by loading the Wasm module code.
  static std::unique_ptr<OakNode> Create(const std::string& module);

  // Performs an Oak Module invocation.
  grpc::Status ProcessModuleInvocation(grpc::GenericServerContext* context,
                                       const std::vector<char>& request_data,
                                       std::vector<char>* response_data);

 private:
  // Clients should construct OakNode instances with Create() (which
  // can fail).
  OakNode(const std::string& module);

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
