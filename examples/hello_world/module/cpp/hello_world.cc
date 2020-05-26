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

#include "oak/module/oak_abi.h"

// TODO(#422): Sort out inclusion of protobuf files
// #include "oak/proto/oak_api.pb.h"

// Local copy of oak_api.pb.h contents for now.
namespace oak {

}  // namespace oak

WASM_EXPORT void grpc_oak_main(oak_abi::Handle _handle) {
  // Create a channel to the gRPC server pseudo-Node.
  oak_abi::Handle write_handle;
  oak_abi::Handle read_handle;
  oak_abi::OakStatus result = channel_create(&write_handle, &read_handle, nullptr, 0);
  if (result != oak_abi::OakStatus::OK) {
    return;
  }

  // Create a gRPC server pseudo-Node
  char config_name[] = "grpc-server";
  result = node_create((uint8_t*)config_name, sizeof(config_name) - 1, nullptr, 0, nullptr, 0,
                       read_handle);
  if (result != oak_abi::OakStatus::OK) {
    return;
  }
  channel_close(read_handle);

  // Create a separate channel for receiving invocations and pass it to the gRPC pseudo-Node.
  oak_abi::Handle grpc_out_handle;
  oak_abi::Handle grpc_in_handle;
  result = channel_create(&grpc_out_handle, &grpc_in_handle, nullptr, 0);
  if (result != oak_abi::OakStatus::OK) {
    return;
  }
  result = channel_write(write_handle, nullptr, 0, (uint8_t*)&grpc_out_handle, 1);
  if (result != oak_abi::OakStatus::OK) {
    return;
  }
  channel_close(grpc_out_handle);
  channel_close(write_handle);

  // TODO(#744): Add C++ helpers for dealing with handle notification space.
  uint8_t handle_space[9] = {
      static_cast<uint8_t>(grpc_in_handle & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 8) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 16) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 24) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 32) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 40) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 48) & 0xff),
      static_cast<uint8_t>((grpc_in_handle >> 56) & 0xff),
      0x00,  // read ready?
  };

  while (true) {
    result = wait_on_channels(handle_space, 1);
    if (result != oak_abi::OakStatus::OK) {
      return;
    }

    // Reading from main channel should give no data and a (read, write) pair of handles.
    uint32_t actual_size;
    uint32_t handle_count;
    oak_abi::Handle handles[2];
    channel_read(grpc_in_handle, nullptr, 0, &actual_size, handles, 2, &handle_count);
    if ((actual_size != 0) || (handle_count != 2)) {
      return;
    }
    oak_abi::Handle req_handle = handles[0];
    oak_abi::Handle rsp_handle = handles[1];

    // Read an incoming request from the read handle, expecting data but no handles.
    // (However, ignore its contents for now).
    uint8_t buf[256];
    channel_read(req_handle, buf, sizeof(buf), &actual_size, nullptr, 0, &handle_count);
    channel_close(req_handle);

    // Manually create an encapsulated GrpcResponse protobuf and send it back.
    //    0a                 b00001.010 = tag 1 (GrpcResponse.rsp_msg), length-delimited field
    //    0b                 length=11
    //      0A                 b00001.010 = tag 1 (HelloResponse.reply), length-delimited field
    //      07                 length=7
    //        74657374696e67   "testing"
    //    18                 b00011.000 = tag 3 (GrpcResponse.last), varint
    //    01                 true
    uint8_t rsp_buf[] = "\x0a\x0b\x0A\x07\x74\x65\x73\x74\x69\x6e\x67\x18\x01";
    // TODO(#422): replace with use of message type and serialization.
    channel_write(rsp_handle, rsp_buf, sizeof(rsp_buf) - 1, nullptr, 0);
    channel_close(rsp_handle);
  }
}
