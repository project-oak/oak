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
#include <random>

#include "oak/server/node_thread.h"
#include "src/interp/interp.h"

namespace oak {

class WasmNode final : public NodeThread {
 public:
  // Creates a Wasm Node by loading the Wasm module code.
  static std::unique_ptr<WasmNode> Create(BaseRuntime* runtime, const std::string& name,
                                          const std::string& module,
                                          const std::string& main_entrypoint);

 private:
  // Clients should construct WasmNode instances with Create() (which can fail).
  WasmNode(BaseRuntime* runtime, const std::string& name, const std::string& main_entrypoint);

  void InitEnvironment(wabt::interp::Environment* env);

  // Return a (borrowed) pointer to the Web Assembly module for the Node.
  wabt::interp::Module* Module() { return env_.GetLastModule(); }

  void Run(Handle handle) override;

  // Native implementation of the `oak.channel_read` host function.
  wabt::interp::HostFunc::Callback OakChannelRead(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_write` host function.
  wabt::interp::HostFunc::Callback OakChannelWrite(wabt::interp::Environment* env);

  // Native implementation of the `oak.wait_on_channels` host function.
  wabt::interp::HostFunc::Callback OakWaitOnChannels(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_create` host function.
  wabt::interp::HostFunc::Callback OakChannelCreate(wabt::interp::Environment* env);

  // Native implementation of the `oak.channel_close` host function.
  wabt::interp::HostFunc::Callback OakChannelClose(wabt::interp::Environment* env);

  // Native implementation of the `oak.node_create` host function.
  wabt::interp::HostFunc::Callback OakNodeCreate(wabt::interp::Environment* env);

  // Native implementation of the `oak.random_get` host function.
  wabt::interp::HostFunc::Callback OakRandomGet(wabt::interp::Environment* env);

  const std::string main_entrypoint_;

  wabt::interp::Environment env_;

  // When running under the Intel Linux SGX stack, std::random_device will pull
  // from /dev/urandom:
  //   https://github.com/intel/linux-sgx/blob/master/sdk/tlibcxx/include/random#L3499
  // Asylo intercepts /dev/[u]random:
  //   https://github.com/google/asylo/blob/master/asylo/platform/posix/io/random_devices.cc
  // and pulls from the RDRAND instruction:
  //   https://github.com/google/asylo/blob/master/asylo/platform/primitives/sgx/hardware_random_sgx_hw.cc
  std::random_device prng_engine_;
};

}  // namespace oak

#endif  // OAK_SERVER_WASM_NODE_H_
