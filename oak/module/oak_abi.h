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

#ifndef OAK_MODULE_OAK_ABI_H_
#define OAK_MODULE_OAK_ABI_H_

#include <stdint.h>

#define WASM_EXPORT extern "C" __attribute__((visibility("default")))
#define WASM_IMPORT(module_name) extern "C" __attribute__((import_module(module_name)))

// Types and enum values used on the Oak ABI.
namespace oak_abi {

using Handle = uint64_t;

enum OakStatus : uint32_t {
  OAK_STATUS_UNSPECIFIED = 0,
  OK = 1,
  ERR_BAD_HANDLE = 2,
  ERR_INVALID_ARGS = 3,
  ERR_CHANNEL_CLOSED = 4,
  ERR_BUFFER_TOO_SMALL = 5,
  ERR_OUT_OF_RANGE = 6,
  ERR_INTERNAL = 7,
};

}  // namespace oak_abi

// Function declarations for the host functions available on the Oak ABI.
WASM_IMPORT("oak") oak_abi::OakStatus wait_on_channels(uint8_t* buff, int32_t count);
WASM_IMPORT("oak")
oak_abi::OakStatus channel_read(oak_abi::Handle handle, uint8_t* buff, size_t usize,
                                uint32_t* actual_size, oak_abi::Handle* handle_buff,
                                size_t handle_count, uint32_t* actual_handle_count);
WASM_IMPORT("oak")
oak_abi::OakStatus channel_write(oak_abi::Handle handle, uint8_t* buff, size_t usize,
                                 uint8_t* handle_buff, size_t handle_count);
WASM_IMPORT("oak") oak_abi::OakStatus channel_close(oak_abi::Handle handle);
WASM_IMPORT("oak")
oak_abi::OakStatus channel_create(oak_abi::Handle* write_handle, oak_abi::Handle* read_handle,
                                  uint8_t* label_buf, size_t label_size);
WASM_IMPORT("oak")
oak_abi::OakStatus node_create(uint8_t* config_buf, size_t config_size, uint8_t* label_buf,
                               size_t label_size, oak_abi::Handle handle);
WASM_IMPORT("oak")
oak_abi::OakStatus random_get(uint8_t* buf, size_t buf_size);

#endif  // OAK_MODULE_OAK_ABI_H_
