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

#include <cmath>
#include <cstdint>

#include "testing/tflite_micro/transformer_expression/transformer_expression_model_data.h"
#include "tflite_micro.h"

namespace {
enum {
  kSuccess = 0,
  kInAccurateAtBase = 1,
  kErrorBase = 200,
  kErrorInit = kErrorBase + 1,
  kErrorRun = kErrorBase + 2,
};

constexpr struct TestData {
  int input[10];
  // [0..2]: output tensor[0]
  // [3..107]: output tensor[1]
  // [108..110]: the first three elements of output tensor[2]
  float expected[111];
} testdata[] = {
#include "testing/tflite_micro/transformer_expression/testdata.c"
};

// Allow the model to use up to 1GB memory.
constexpr int kTensorArenaSize = 1024 * 1024 * 1024;
uint8_t tensor_arena[kTensorArenaSize];

bool IsEqual(float a, float b, float epsilon = 1e-6) { return fabsf(a - b) <= epsilon; }
}  // namespace

int main(int argc, char* argv[]) {
  // output tensor[0]: float * 3
  // output tensor[1]: float * 105
  // output tensor[2]: float * 4522
  // Three tensors' outputs are stored in the 4630-floats output in order.
  float output[4630] = {.0f};

  size_t output_buffer_len = 0;
  if (tflite_init(g_transformer_expression_model_data, g_transformer_expression_model_data_size,
                  tensor_arena, kTensorArenaSize, &output_buffer_len) != 0) {
    return kErrorInit;
  }

  constexpr size_t num_of_expected =
      sizeof(((struct TestData*)0)->expected) / sizeof(((struct TestData*)0)->expected[0]);
  for (size_t i = 0; i < sizeof(testdata) / sizeof(testdata[0]); i++) {
    const uint8_t* input = reinterpret_cast<const uint8_t*>(testdata[i].input);
    const size_t input_bytes = sizeof(testdata[i].input);
    size_t output_len = 0;
    if (tflite_run(input, input_bytes, reinterpret_cast<uint8_t*>(&output[0]), &output_len) != 0) {
      return kErrorRun;
    }

    // Check accuracy, if it's inaccurate at the Nth record, return N.
    // At shell, echo $? to get the number if inaccuracy was found.
    for (size_t j = 0; j < num_of_expected; j++) {
      if (!IsEqual(output[j], testdata[i].expected[j])) {
        return kInAccurateAtBase + i;
      }
    }
  }

  return kSuccess;
}
