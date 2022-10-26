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

#ifndef CC_TFLITE_MICRO_MODEL_H_
#define CC_TFLITE_MICRO_MODEL_H_

#include <stddef.h>
#include <stdint.h>

// TODO(#3297): Don't use null terminated and use `string_view` instead.
/// Wrapper for the `oak_log_debug` that counts the length of the message
/// before sending it to the Rust logger.
void tflite_log_debug(const char* message);

#ifdef __cplusplus
extern "C" {
#endif

int tflite_init(const uint8_t* model_bytes_ptr, size_t model_bytes_len,
                const uint8_t* tensor_arena_bytes_ptr, size_t tensor_arena_bytes_len,
                size_t* output_buffer_len_ptr);

int tflite_run(const uint8_t* input_bytes_ptr, size_t input_bytes_len, uint8_t* output_bytes_ptr,
               size_t* output_bytes_len_ptr);

void oak_log_debug(const char* message_ptr, size_t message_len);

#ifdef __cplusplus
}
#endif

#endif  // CC_TFLITE_MICRO_MODEL_H_
