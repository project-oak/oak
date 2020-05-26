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

#include "oak/module/oak_abi.h"
#include "oak/module/placeholders.h"
#include "tensorflow/lite/interpreter.h"
#include "tensorflow/lite/kernels/register.h"
#include "tensorflow/lite/model.h"
#include "tensorflow/lite/optional_debug_tools.h"

// Include standard C++ placeholder oak_main() implementation.
#include "oak/module/oak_main.h"

const char kModelBuffer[] = {
    0x18, 0x00, 0x00, 0x00, 0x54, 0x46, 0x4c, 0x33, 0x00, 0x00, 0x0e, 0x00, 0x14, 0x00, 0x04,
    0x00, 0x08, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x10, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x03, 0x00,
    0x00, 0x00, 0x44, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x14, 0x00, 0x04, 0x00, 0x08, 0x00,
    0x0c, 0x00, 0x10, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x18, 0x00, 0x00,
    0x00, 0x0c, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00, 0x08, 0x00, 0x04, 0x00,
    0x06, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

std::string init_tensorflow() {
  // Load model.
  std::unique_ptr<tflite::FlatBufferModel> model = tflite::FlatBufferModel::BuildFromBuffer(
      reinterpret_cast<const char*>(&kModelBuffer), sizeof(kModelBuffer));
  if (model == nullptr) {
    return std::string("Error: Model was not loaded successfully");
  }

  // Build the interpreter.
  tflite::ops::builtin::BuiltinOpResolver resolver;
  tflite::InterpreterBuilder builder(*model, resolver);
  std::unique_ptr<tflite::Interpreter> interpreter;
  builder(&interpreter);
  if (interpreter == nullptr) {
    return std::string("Error: Interpreter was not created successfully");
  }

  // Allocate tensor buffers.
  if (interpreter->AllocateTensors() != kTfLiteOk) {
    return std::string("Error: Tensors were not allocated successfully");
  }

  // Run inference.
  if (interpreter->Invoke() != kTfLiteOk) {
    return std::string("Error: Interpreter was not invoked successfully");
  }

  return std::string("Success: Model was loaded correctly");
}

extern "C" void process_invocation(const uint8_t* _req_buf, uint32_t _req_size,
                                   oak_abi::Handle rsp_handle) {
  init_tensorflow();

  // Manually create an encapsulated GrpcResponse protobuf and send it back.
  //    0a                 b00001.010 = tag 1 (GrpcResponse.rsp_msg), length-delimited field
  //    0b                 length=11
  //      12                 b00010.010 = tag 2 (Any.value), length-delimited field
  //      09                 length=9
  //        0A                 b00001.010 = tag 1 (HelloResponse.reply), length-delimited field
  //        07                 length=7
  //          74657374696e67   "testing"
  //    18                 b00011.000 = tag 3 (GrpcResponse.last), varint
  //    01                 true
  uint8_t rsp_buf[] = "\x0a\x0b\x12\x09\x0A\x07\x74\x65\x73\x74\x69\x6e\x67\x18\x01";
  // TODO(#422): replace with use of message type and serialization.
  channel_write(rsp_handle, rsp_buf, sizeof(rsp_buf) - 1, nullptr, 0);
}
