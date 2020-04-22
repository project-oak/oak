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

#ifndef OAK_SERVER_RUST_OAK_GLUE_H_
#define OAK_SERVER_RUST_OAK_GLUE_H_

#include <cstdint>

extern "C" {

// Perform start of day initialization.  Must only be called once, before
// any other functions.  The debug flag is treated as a boolean indicating
// whether debug logging should be enabled for Rust.
void glue_init(uint32_t debug);

// Function pointer used for up-calling from Rust to C++ to create and run a pseudo-Node.
// - The data parameter has the factory_data value registered at glue_start.
// - [name, name+name_len) gives the config name for the Node to be started.
// - node_id should be used for all glue_<fn>() invocations by the new Node.
// - handle is a read half of an initial channel.
typedef void (*node_factory)(uintptr_t data, const char* name, uint32_t name_len, uint64_t node_id,
                             uint64_t handle);

// Start the Rust runtime, passing a serialized ApplicationConfiguration
// protobuf message.  Fills in node_id with the NodeId value for the implicitly
// created initial Node (which is used to run the gRPC server pseudo-Node under),
// and returns the initial write handle (which is used to send in gRPC invocations
// to the first Application Node).
uint64_t glue_start(const uint8_t* config_buf, uint32_t config_len, node_factory factory,
                    uintptr_t factory_data, uint64_t* node_id);
// Stop the Rust runtime.
void glue_stop();

// The following functions are analogous to those on the Oak ABI, with the
// addition of an initial node_id parameter that identifies the Node performing
// the operation.
uint32_t glue_wait_on_channels(uint64_t node_id, uint8_t* buf, uint32_t count);
uint32_t glue_channel_read(uint64_t node_id, uint64_t handle, uint8_t* buf, uint32_t size,
                           uint32_t* actual_size, uint8_t* handle_buf, uint32_t handle_count,
                           uint32_t* actual_handle_count);
uint32_t glue_channel_write(uint64_t node_id, uint64_t handle, const uint8_t* buf, uint32_t size,
                            const uint8_t* handle_buf, uint32_t handle_count);
uint32_t glue_channel_create(uint64_t node_id, uint64_t* write, uint64_t* read);
uint32_t glue_channel_close(uint64_t node_id, uint64_t handle);

// Size of per-handle buffer for wait_on_channels (one 8-byte handle plus one
// byte for status).
const uint32_t kSpaceBytesPerHandle = 9;
}  // extern "C"

#endif  // OAK_SERVER_RUST_OAK_GLUE_H_
