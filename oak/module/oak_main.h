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

#ifndef OAK_MODULE_OAK_MAIN_H_
#define OAK_MODULE_OAK_MAIN_H_

// TODO(#744): sort out linker problems with including this as a cc_library(alwayslink=1) target.

#include <stddef.h>
#include <stdint.h>

#include "oak/module/oak_abi.h"

extern "C" void process_invocation(const uint8_t* req_buf, uint32_t req_size,
                                   oak_abi::Handle rsp_handle);

// TODO(#422): Sort out inclusion of protobuf files
// #include "proto/oak_api.pb.h"

// Placeholder main entrypoint for C++ Oak Modules that have simple unary
// method semantics.  The Oak Module needs to provide an implementation
// of the `process_invocation()` function, which will be called with
// each incoming request.
WASM_EXPORT void oak_main(oak_abi::Handle _handle) {
  // Create a channel to the gRPC server pseudo-Node.
  oak_abi::Handle write_handle;
  oak_abi::Handle read_handle;
  oak_abi::OakStatus result = channel_create(&write_handle, &read_handle, nullptr, 0);
  if (result != oak_abi::OakStatus::OK) {
    return;
  }

  // Create a gRPC server pseudo-Node
  // Manually create an encapsulated NodeConfiguration protobuf and send it back.
  //    0a                     b00001.010 = tag 1 (NodeConfiguration.name), length-delimited field
  //    0b                     length=11
  //      677270635f736572     "grpc_server"
  //    2a                     b00101.010 = tag 5 (NodeConfiguration.grpc_server_config)
  //    0b                     length=11
  //      0a                   b00001.010 = tag 1 (GrpcServerConfiguration.address)
  //      09                   length=9
  //        5b3a3a5d3a38303830 "[::]:8080"
  char node_config[] =
      "\x0a\x0b\x67\x72\x70\x63\x5f\x73\x65\x72\x76\x65\x72\x2a\x0b\x0a\x09\x5b\x3a\x3a\x5d\x3a\x38"
      "\x30\x38\x30";
  result = node_create((uint8_t*)node_config, sizeof(node_config) - 1, nullptr, 0, read_handle);
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
    // TODO(#744): cope with requests bigger than 1k.
    uint8_t buf[1024];
    channel_read(req_handle, buf, sizeof(buf), &actual_size, nullptr, 0, &handle_count);
    channel_close(req_handle);

    // Invoke the externally-provided function to process the method invocation.
    process_invocation(buf, actual_size, rsp_handle);

    channel_close(rsp_handle);
  }
}

#endif  // OAK_MODULE_OAK_MAIN_H_
