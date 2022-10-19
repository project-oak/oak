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

#include <stddef.h>
#include <stdint.h>
#include <string.h>

void tflite_log_debug(const char* message) { oak_log_debug(message, strlen(message)); }

// TODO(#3297): Implement TensorFlow Lite initialization logic.
int tflite_init(const uint8_t* model_bytes, size_t model_bytes_len,
                const uint8_t* tensor_arena_bytes, size_t tensor_arena_bytes_len) {
  tflite_log_debug("Initializing TensorFlow Lite");
  return 0;
}

// TODO(#3297): Implement TensorFlow Lite inference logic.
int tflite_run(const uint8_t* input_bytes, size_t input_bytes_len, uint8_t* output_bytes,
               size_t* output_bytes_len) {
  tflite_log_debug("Running TensorFlow Lite inference");
  return 0;
}
