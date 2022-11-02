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

#include "output_handler.h"
#include "tflite_micro.h"

#include "cc/tflite_micro/apps/hello_world/hello_world_model_data.h"
#include "tensorflow/lite/micro/all_ops_resolver.h"
#include "tensorflow/lite/micro/micro_error_reporter.h"
#include "tensorflow/lite/micro/micro_allocator.h"
#include "tensorflow/lite/micro/micro_interpreter.h"
#include "tensorflow/lite/schema/schema_generated.h"

namespace {


const tflite::Model* model = nullptr;
tflite::MicroInterpreter* interpreter = nullptr;
TfLiteTensor* input = nullptr;
TfLiteTensor* output = nullptr;
}

int tflite_init(
    const uint8_t* model_bytes_ptr, size_t model_bytes_len,
    uint8_t* tensor_arena_bytes_ptr, size_t tensor_arena_bytes_len,
    size_t* output_buffer_len_ptr) {
  // Map the model into a usable data structure. This doesn't involve any
  // copying or parsing, it's a very lightweight operation.
  model = tflite::GetModel(g_hello_world_model_data);

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
  *output_buffer_len_ptr = sizeof(float);

  return 0;
}

int tflite_run(
    const uint8_t* input_bytes_ptr, size_t input_bytes_len,
    uint8_t* output_bytes_ptr, size_t* output_bytes_len_ptr) { 
  if (!input_bytes_ptr || !output_bytes_ptr || !output_bytes_len_ptr) {
    MicroPrintf("Invalid parameters\n");
    return -1;
  }

  if (input_bytes_len != sizeof(float)) {
    MicroPrintf("Expected input len: %d bytes but got %d bytes\n",
                sizeof(float),
                input_bytes_len);
    return -1;
  }
  auto x = *reinterpret_cast<const float*>(input_bytes_ptr);

  // Quantize the input from floating-point to integer
  int8_t x_quantized = x / input->params.scale + input->params.zero_point;
  // Place the quantized input in the model's input tensor
  input->data.int8[0] = x_quantized;

  // Run inference, and report any error
  TfLiteStatus invoke_status = interpreter->Invoke();
  if (invoke_status != kTfLiteOk) {
    MicroPrintf("Invoke failed on x: %f\n", static_cast<double>(x));
    return -1;
  }

  // Obtain the quantized output from model's output tensor
  int8_t y_quantized = output->data.int8[0];
  // Dequantize the output from integer to floating-point
  float y = (y_quantized - output->params.zero_point) * output->params.scale;

  // Output the results. A custom HandleOutput function can be implemented
  // for each supported hardware target.
  HandleOutput(x, y);

  // Send output back through Oak kenrel and TF runtime.
  *reinterpret_cast<float*>(output_bytes_ptr) = y;
  *output_bytes_len_ptr = sizeof(y);

  return 0;
}
