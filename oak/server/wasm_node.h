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

#ifndef OAK_SERVER_WASM_NODE_H_
#define OAK_SERVER_WASM_NODE_H_

#include <memory>

#include "oak/server/node_thread.h"
#include "src/interp/interp.h"

namespace oak {

class WasmNode final : public NodeThread {
 public:
  // Creates a Wasm Node by loading the Wasm module code.
  static std::unique_ptr<WasmNode> Create(const std::string& name, const std::string& module);

 private:
  // Clients should construct WasmNode instances with Create() (which can fail).
  WasmNode(const std::string& name);

  void InitEnvironment(wabt::interp::Environment* env);

  void Run() override;

  // Native implementation of the `oak.channel_read` host function.
  wabt::interp::HostFunc::Callback OakChannelRead(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_write` host function.
  wabt::interp::HostFunc::Callback OakChannelWrite(wabt::interp::Environment* env);

  // Native implementation of the `oak.wait_on_channels` host function.
  wabt::interp::HostFunc::Callback OakWaitOnChannels(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_close` host function.
  wabt::interp::HostFunc::Callback OakChannelClose(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_find` host function.
  wabt::interp::HostFunc::Callback OakChannelFind(wabt::interp::Environment* env);

  wabt::interp::Environment env_;
  // TODO: Use smart pointers.
  wabt::interp::DefinedModule* module_;
};

}  // namespace oak

#endif  // OAK_SERVER_WASM_NODE_H_
