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
#include "oak/module/defines.h"  // for imports and exports

WASM_IMPORT("oak") int wait_on_channels(uint8_t* buff, int32_t count);
WASM_IMPORT("oak")
int channel_read(uint64_t handle, uint8_t* buff, size_t usize, uint32_t* actual_size);
WASM_IMPORT("oak") int channel_write(uint64_t handle, uint8_t* buff, size_t usize);

WASM_EXPORT void oak_main() {
  uint8_t handle_space[9] = {oak::GRPC_IN_CHANNEL_HANDLE, 0, 0, 0, 0, 0, 0, 0, 0};
  uint8_t _buf[256];
  uint32_t actual_size;

  while (true) {
    wait_on_channels(handle_space, 1);

    channel_read(oak::GRPC_IN_CHANNEL_HANDLE, _buf, sizeof(_buf), &actual_size);

    // Encapsulated GrpcResponse protobuf.
    //    12                 b00010.010 = tag 2 (GrpcResponse.rsp_msg), length-delimited field
    //    0b                 length=11
    //      12                 b00010.010 = tag 2 (Any.value), length-delimited field
    //      09                 length=9
    //        0A                 b00001.010 = tag 1 (HelloResponse.reply), length-delimited field
    //        07                 length=7
    //          74657374696e67   "testing"
    //    20                 b00100.000 = tag 4 (GrpcResponse.last), varint
    //    01                 true
    uint8_t buf[] = "\x12\x0b\x12\x09\x0A\x07\x74\x65\x73\x74\x69\x6e\x67\x20\x01";
    // TODO: replace with use of message type and serialization.
    channel_write(oak::GRPC_OUT_CHANNEL_HANDLE, buf, sizeof(buf) - 1);
  }
}
