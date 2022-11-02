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

#include <stdint.h>

namespace {
// This constant represents the range of x values our model was trained on,
// which is from 0 to (2 * Pi). We approximate Pi to avoid requiring additional
// libraries.
const float kXrange = 2.f * 3.14159265359f;

// This constant determines the number of inferences to perform across the range
// of x values defined above. Since each inference takes time, the higher this
// number, the more time it will take to run through the entire range. The value
// of this constant can be tuned so that one full cycle takes a desired amount
// of time. Since different devices take different amounts of time to perform
// inference, this value should be defined per-device.
//
// This is a small number so that it's easy to read the logs
const int kInferencesPerCycle = 20;

constexpr int kTensorArenaSize = 2048;
uint8_t tensor_arena[kTensorArenaSize];

int inference_count = 0;
}

int main(int argc, char* argv[]) {
  size_t output_buffer_len = 0;

  // We don't use model_bytes_ptr and model_bytes_len for hello_world
  // tflite model as the model is built in as a static cc array.
  if (tflite_init(nullptr /*model_bytes_ptr*/,
                  0 /*model_bytes_len*/,
                  tensor_arena,
                  kTensorArenaSize,
                  &output_buffer_len) == 0) {
    float output = 0.f;
    size_t output_len = 0;
    while (sizeof(output) == output_buffer_len) {
      // Calculate an x value to feed into the model. We compare the current
      // inference_count to the number of inferences per cycle to determine
      // our position within the range of possible x values the model was
      // trained on, and use this to calculate a value.
      float position = static_cast<float>(inference_count) /
                       static_cast<float>(kInferencesPerCycle);
      float x = position * kXrange;
      if (tflite_run(reinterpret_cast<const uint8_t*>(&x),
                     sizeof(x),
                     reinterpret_cast<uint8_t*>(&output),
                     &output_len) != 0) {
        break;
      }

      // Increment the inference_counter, and reset it if we have reached
      // the total number per cycle.
      inference_count = (inference_count + 1) % kInferencesPerCycle;
    }
  }

  return 0;
}
