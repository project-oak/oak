/*
 * Copyright 2022 The Project Oak Authors
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

#include "tflite_micro.h"

#include "tensorflow/lite/micro/all_ops_resolver.h"
#include "tensorflow/lite/micro/micro_error_reporter.h"
#include "tensorflow/lite/micro/micro_allocator.h"
#include "tensorflow/lite/micro/micro_interpreter.h"
#include "tensorflow/lite/schema/schema_generated.h"

TfLiteTensor* input = nullptr;
TfLiteTensor* output = nullptr;

namespace {
const tflite::Model* model = nullptr;
tflite::MicroInterpreter* interpreter = nullptr;
}

const TfLiteTensor* tflite_get_input_tensor() {
    return input;
}

const TfLiteTensor* tflite_get_output_tensor() {
    return output;
}

int tflite_init(
    const uint8_t* model_bytes_ptr, size_t model_bytes_len,
    uint8_t* tensor_arena_bytes_ptr, size_t tensor_arena_bytes_len,
    size_t* output_buffer_len_ptr) {
  if (!model_bytes_ptr
    || !model_bytes_len
    || !tensor_arena_bytes_ptr
    || !tensor_arena_bytes_len
    || !output_buffer_len_ptr) {
    MicroPrintf("tflite_init: Invalid parameters\n");
    return -1;
  }

  // Map the model into a usable data structure. This doesn't involve any
  // copying or parsing, it's a very lightweight operation.
  model = tflite::GetModel(model_bytes_ptr);

  // This pulls in all the operation implementations we need.
  // NOLINTNEXTLINE(runtime-global-variables)
  static tflite::AllOpsResolver resolver;

  // Build an interpreter to run the model with.
  static tflite::MicroInterpreter static_interpreter(
      model, resolver, tensor_arena_bytes_ptr, tensor_arena_bytes_len);
  interpreter = &static_interpreter;

  // Allocate memory from the tensor_arena for the model's tensors.
  TfLiteStatus allocate_status = interpreter->AllocateTensors();
  if (allocate_status != kTfLiteOk) {
    MicroPrintf("AllocateTensors() failed");
    return -1;
  }

  // Obtain pointers to the model's input and output tensors.
  input = interpreter->input(0);
  output = interpreter->output(0);

  // Request a fixed-size output buffer from Oak kernel and TF runtime,
  // which will be passed in at tflite_run(..., output_bytes_ptr, ...).
  *output_buffer_len_ptr = output->bytes;

  return 0;
}

int tflite_run(
    const uint8_t* input_bytes_ptr, size_t input_bytes_len,
    uint8_t* output_bytes_ptr, size_t* output_bytes_len_ptr) { 
  if (!input_bytes_ptr
    || !input_bytes_len
    || !output_bytes_ptr
    || !output_bytes_len_ptr) {
    MicroPrintf("tflite_run: Invalid parameters\n");
    return -1;
  }

  if (input_bytes_len != input->bytes) {
    MicroPrintf("Expected input len: %d bytes but got %d bytes\n",
                input->bytes,
                input_bytes_len);
    return -1;
  }

  // Place input in the model's input tensors
  memcpy(input->data.uint8, input_bytes_ptr, input_bytes_len);

  // Run inference, and report any error
  TfLiteStatus invoke_status = interpreter->Invoke();
  if (invoke_status != kTfLiteOk) {
    MicroPrintf("Invoke failed, err: %d\n", invoke_status);
    return -1;
  }

  // Send output tensors back through Oak TF runtime
  memcpy(output_bytes_ptr, output->data.uint8, output->bytes);
  *output_bytes_len_ptr = output->bytes;

  return 0;
}
