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

//#include "examples/tensorflow/proto/tensorflow.grpc.pb.h"
//#include "examples/tensorflow/proto/tensorflow.pb.h"
#include "oak/module/defines.h"  // for imports and exports
//#include "oak/proto/oak_api.pb.h"
#include "tensorflow/lite/interpreter.h"
#include "tensorflow/lite/kernels/register.h"
#include "tensorflow/lite/model.h"
#include "tensorflow/lite/optional_debug_tools.h"

// Local copy of oak_api.pb.h contents for now.
namespace oak {

enum OakStatus {
  OAK_STATUS_UNSPECIFIED = 0,
  OK = 1,
  ERR_BAD_HANDLE = 2,
  ERR_INVALID_ARGS = 3,
  ERR_CHANNEL_CLOSED = 4,
  ERR_BUFFER_TOO_SMALL = 5,
  ERR_OUT_OF_RANGE = 6,
  ERR_INTERNAL = 7,
};

}  // namespace oak

WASM_IMPORT("oak") uint32_t wait_on_channels(uint8_t* buff, int32_t count);
WASM_IMPORT("oak")
uint32_t channel_read(uint64_t handle, uint8_t* buff, size_t usize, uint32_t* actual_size,
                      uint64_t* handle_buff, size_t handle_count, uint32_t* actual_handle_count);
WASM_IMPORT("oak")
uint32_t channel_write(uint64_t handle, uint8_t* buff, size_t usize, uint8_t* handle_buff,
                       size_t handle_count);
WASM_IMPORT("oak") uint32_t channel_close(uint64_t handle);

WASM_EXPORT int32_t oak_main(uint64_t grpc_in_handle) {
  char grpc_in_name[] = "grpc_in";
  char grpc_out_name[] = "grpc_out";
  uint8_t handle_space[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
  uint8_t _buf[256];
  uint32_t actual_size;
  uint32_t handle_count;

  // TODO: Add C++ helpers for dealing with handle notification space.
  handle_space[0] = grpc_in_handle & 0xff;
  handle_space[1] = (grpc_in_handle >> 8) & 0xff;
  handle_space[2] = (grpc_in_handle >> 16) & 0xff;
  handle_space[3] = (grpc_in_handle >> 24) & 0xff;
  handle_space[4] = (grpc_in_handle >> 32) & 0xff;
  handle_space[5] = (grpc_in_handle >> 40) & 0xff;
  handle_space[6] = (grpc_in_handle >> 48) & 0xff;
  handle_space[7] = (grpc_in_handle >> 56) & 0xff;
  handle_space[8] = 0x00;  // read ready?

  while (true) {
    int32_t result = wait_on_channels(handle_space, 1);
    if (result != oak::OakStatus::OK) {
      return result;
    }

    uint64_t rsp_handle;
    channel_read(grpc_in_handle, _buf, sizeof(_buf), &actual_size, &rsp_handle, 1, &handle_count);

    uint8_t buf[] = "\x0a\x0b\x12\x09\x0A\x07\x74\x65\x73\x74\x69\x6e\x67\x18\x01";
    // TODO: replace with use of message type and serialization.
    channel_write(rsp_handle, buf, sizeof(buf) - 1, nullptr, 0);
    channel_close(rsp_handle);
  }
  return oak::OakStatus::OK;
}

const char* kModelBuffer = "";
/*
std::string init_tensorflow() {
  // Load model.
  std::unique_ptr<tflite::FlatBufferModel> model = BuildFromBuffer(
      kModelBuffer, kModelBufferSize);
  if (model == nullptr) {
    return std::string("Error: Model was not loaded successfully");
  }

  // Build the interpreter.
  tflite::ops::builtin::BuiltinOpResolver resolver;
  InterpreterBuilder builder(*model, resolver);
  std::unique_ptr<Interpreter> interpreter;
  builder(&interpreter);
  if (interpreter == nullptr) {
    return std::string("Error: Interpreter was not created successfully");
  }

  // Allocate tensor buffers.
  if (interpreter->AllocateTensors() != kTfLiteOk) {
    //printf("=== Pre-invoke Interpreter State ===\n");
    //tflite::PrintInterpreterState(interpreter.get());
    return std::string("Error: Tensors were not allocated successfully");
  }

  // Run inference.
  if (interpreter->Invoke() != kTfLiteOk) {
    //printf("\n\n=== Post-invoke Interpreter State ===\n");
    //tflite::PrintInterpreterState(interpreter.get());
    return std::string("Error: Interpreter was not invoked successfully");
  }
}*/
