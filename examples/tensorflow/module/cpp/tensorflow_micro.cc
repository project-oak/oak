/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/module/defines.h"  // for imports and exports
#include "oak/module/placeholders.h"
#include "tensorflow/lite/micro/kernels/all_ops_resolver.h"
#include "tensorflow/lite/micro/micro_interpreter.h"

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

// Constants were taken from the TFLite exapmles:
// https://github.com/tensorflow/tensorflow/blob/11bed638b14898cdde967f6b108e45732aa4798a/tensorflow/lite/micro/examples/network_tester/network_tester_test.cc#L25
// https://github.com/tensorflow/tensorflow/blob/11bed638b14898cdde967f6b108e45732aa4798a/tensorflow/lite/micro/examples/network_tester/network_model.h#L16-L64
const uint16_t kTensorArenaSize 1024

const unsigned char kModelBuffer[] = {
    0x18, 0x00, 0x00, 0x00, 0x54, 0x46, 0x4c, 0x33, 0x00, 0x00, 0x0e, 0x00,
    0x18, 0x00, 0x04, 0x00, 0x08, 0x00, 0x0c, 0x00, 0x10, 0x00, 0x14, 0x00,
    0x0e, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x08, 0x02, 0x00, 0x00,
    0x0c, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x38, 0x00, 0x00, 0x00, 0x0f, 0x00, 0x00, 0x00,
    0x54, 0x4f, 0x43, 0x4f, 0x20, 0x43, 0x6f, 0x6e, 0x76, 0x65, 0x72, 0x74,
    0x65, 0x64, 0x2e, 0x00, 0x03, 0x00, 0x00, 0x00, 0x18, 0x00, 0x00, 0x00,
    0x0c, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0xf8, 0xff, 0xff, 0xff,
    0xfc, 0xff, 0xff, 0xff, 0x04, 0x00, 0x04, 0x00, 0x04, 0x00, 0x00, 0x00,
    0xf8, 0xfe, 0xff, 0xff, 0x20, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00,
    0x08, 0x00, 0x00, 0x00, 0x3c, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x02, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x94, 0x00, 0x00, 0x00,
    0x7e, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x03, 0x10, 0x00, 0x00, 0x00,
    0x02, 0x00, 0x00, 0x00, 0x1c, 0x00, 0x00, 0x00, 0x30, 0x00, 0x00, 0x00,
    0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
    0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x64, 0x61, 0x74, 0x61, 0x2f, 0x50, 0x6c, 0x61, 0x63, 0x65, 0x68, 0x6f,
    0x6c, 0x64, 0x65, 0x72, 0x00, 0x00, 0x00, 0x00, 0x6c, 0xff, 0xff, 0xff,
    0x30, 0x00, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00, 0x18, 0x00, 0x00, 0x00,
    0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x80, 0x3f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7f, 0x43,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0e, 0x00,
    0x18, 0x00, 0x08, 0x00, 0x07, 0x00, 0x0c, 0x00, 0x10, 0x00, 0x14, 0x00,
    0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x10, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x1c, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00,
    0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
    0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00,
    0x70, 0x6f, 0x6f, 0x6c, 0x31, 0x2f, 0x4d, 0x61, 0x78, 0x50, 0x6f, 0x6f,
    0x6c, 0x32, 0x44, 0x2f, 0x4d, 0x61, 0x78, 0x50, 0x6f, 0x6f, 0x6c, 0x00,
    0x0c, 0x00, 0x14, 0x00, 0x04, 0x00, 0x08, 0x00, 0x0c, 0x00, 0x10, 0x00,
    0x0c, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00,
    0x14, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x80, 0x3f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7f, 0x43,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x18, 0x00, 0x00, 0x00, 0x14, 0x00, 0x18, 0x00, 0x00, 0x00, 0x08, 0x00,
    0x0c, 0x00, 0x07, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x14, 0x00,
    0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x10, 0x00, 0x00, 0x00,
    0x14, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0e, 0x00,
    0x18, 0x00, 0x07, 0x00, 0x08, 0x00, 0x0c, 0x00, 0x10, 0x00, 0x14, 0x00,
    0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x00, 0x00, 0x00,
    0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00,
    0x08, 0x00, 0x07, 0x00, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11};

const unsigned char kInputData[] = {1, 2,  3,  4,  5,  6,  7,  8,
                                    9, 10, 11, 12, 13, 14, 15, 16};
const unsigned char kExpectedOutputData[] = {6, 8, 14, 16};

std::string init_tensorflow() {
  const tflite::Model* model = ::tflite::GetModel(kModelBuffer);

  tflite::ops::micro::AllOpsResolver resolver;

  tflite::MicroInterpreter interpreter(model, resolver, tensor_arena,
                                       TENSOR_ARENA_SIZE, error_reporter);
  interpreter.AllocateTensors();

  TfLiteTensor* input = interpreter.input(0);
  memcpy(input->data.uint8, kInputData, input->bytes);

  TfLiteStatus invoke_status = interpreter.Invoke();
  if (invoke_status != kTfLiteOk) {
    return std::string("Error: Interpreter invoke failed");
  }

  TfLiteTensor* output = interpreter.output(0);
  if (memcmp(kExpectedOutputData, output->data.uint8, output->bytes) != 0) {
    return std::string("Error: Model output is incorrect");
  }
  //for (int i = 0; i < output->bytes; ++i) {
  //  success &= (output->data.uint8[i] == kExpectedOutputData[i]);
  //}
  return std::string("Success: Model was loaded correctly");
}

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

    init_tensorflow();

    // Encapsulated GrpcResponse protobuf.
    //    0a                 b00001.010 = tag 1 (GrpcResponse.rsp_msg), length-delimited field
    //    0b                 length=11
    //      12                 b00010.010 = tag 2 (Any.value), length-delimited field
    //      09                 length=9
    //        0A                 b00001.010 = tag 1 (HelloResponse.reply), length-delimited field
    //        07                 length=7
    //          74657374696e67   "testing"
    //    18                 b00011.000 = tag 3 (GrpcResponse.last), varint
    //    01                 true
    uint8_t buf[] = "\x0a\x0b\x12\x09\x0A\x07\x74\x65\x73\x74\x69\x6e\x67\x18\x01";
    // TODO: replace with use of message type and serialization.
    channel_write(rsp_handle, buf, sizeof(buf) - 1, nullptr, 0);
    channel_close(rsp_handle);
  }
  return oak::OakStatus::OK;
}
