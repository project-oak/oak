/*
 * Copyright 2024 The Project Oak Authors
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

#ifndef THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_FFI_H_
#define THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_FFI_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// This is for use with bindgen.  Note that only basic types that work in
// both C and Rust.  The char type is complicated and uint8_t is used instead.
void register_callbacks(
    const uint8_t* (*read_request_cb)(size_t* len),
    bool (*write_response_cb)(const uint8_t* data, size_t len),
    bool (*log_cb)(const uint8_t* data, size_t len),
    const uint8_t* (*storage_get_item_cb)(const uint8_t* key, size_t key_len,
                                          size_t* item_len),
    const uint8_t* (*read_error_cb)(uint32_t* status_code, size_t* len));

void oak_main();

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_FFI_H_
