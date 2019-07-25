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

#include <stddef.h>
#include <stdint.h>

#include "oak/common/handles.h"
#include "oak/common/status.h"
#include "oak/module/defines.h"  // for imports and exports

WASM_IMPORT("oak")
int channel_read(uint64_t handle, uint8_t* buff, size_t usize, uint32_t* actual_size);
WASM_IMPORT("oak") int channel_write(uint64_t handle, uint8_t* buff, size_t usize);

WASM_EXPORT int32_t oak_initialize() { return oak::STATUS_OK; }

WASM_EXPORT int32_t oak_handle_grpc_call() {
  uint8_t _buf[256];
  uint32_t actual_size;
  channel_read(oak::GRPC_IN_CHANNEL_HANDLE, _buf, sizeof(_buf), &actual_size);

  // Hard-coded serialized HelloResponse protobuf that says testing.
  // TODO: replace with use of message type and serialization.
  uint8_t buf[] = "\x0A\x07\x74\x65\x73\x74\x69\x6e\x67";
  channel_write(oak::GRPC_OUT_CHANNEL_HANDLE, buf, sizeof(buf) - 1);
  return oak::STATUS_OK;
}
