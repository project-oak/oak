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

#include <memory>

#include "oak/server/wasm_node.h"

// See https://llvm.org/docs/LibFuzzer.html#fuzz-target.
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  std::string module(reinterpret_cast<char const*>(data), size);
  // Build a WasmNode instance treating the fuzzing input as Wasm module code.
  // No need to pass in an owning runtime instance (first argument) since the
  // built Node is never run.
  std::unique_ptr<oak::WasmNode> node = oak::WasmNode::Create(nullptr, "test", module, "oak_main");
  return 0;
}
