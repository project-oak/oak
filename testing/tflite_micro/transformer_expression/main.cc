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

#include "testing/tflite_micro/transformer_expression/transformer_expression_model_data.h"

#include <stdint.h>

namespace {
// Allow the model to use up to 1GB memory.
constexpr int kTensorArenaSize = 1024 * 1024 * 1024;
uint8_t tensor_arena[kTensorArenaSize];
}

int main(int argc, char* argv[]) {
  // input tensor[0]: int * 10
  int input[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

  // output tensor[0]: float * 3
  // output tensor[1]: float * 105
  // output tensor[2]: float * 4522
  // Three tensors' outputs are stored in the 4630-floats output in order.
  float output[4630] = {.0f};

  size_t output_buffer_len = 0;
  if (tflite_init(g_transformer_expression_model_data,
                  g_transformer_expression_model_data_size,
                  tensor_arena,
                  kTensorArenaSize,
                  &output_buffer_len) == 0) {
    size_t output_len = 0;
    tflite_run(reinterpret_cast<const uint8_t*>(&input[0]),
               sizeof(input),
               reinterpret_cast<uint8_t*>(&output[0]),
               &output_len);
  }

  return 0;
}
