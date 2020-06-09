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

// Include standard C++ placeholder oak_main() implementation.
#include "oak/module/oak_main.h"

extern "C" void process_invocation(const uint8_t* _req_buf, uint32_t _req_size,
                                   oak_abi::Handle rsp_handle) {
  // Ignore the contents of the incoming request.
  // Manually create an encapsulated GrpcResponse protobuf and send it back.
  //    0a                 b00001.010 = tag 1 (GrpcResponse.rsp_msg), length-delimited field
  //    09                 length=9
  //      0a                 b00001.010 = tag 1 (HelloResponse.reply), length-delimited field
  //      07                 length=7
  //        74657374696e67   "testing"
  //    18                 b00011.000 = tag 3 (GrpcResponse.last), varint
  //    01                 true
  uint8_t rsp_buf[] = "\x0a\x09\x0a\x07\x74\x65\x73\x74\x69\x6e\x67\x18\x01";
  // TODO(#422): replace with use of message type and serialization.
  channel_write(rsp_handle, rsp_buf, sizeof(rsp_buf) - 1, nullptr, 0);
}
