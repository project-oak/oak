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

#include "cc/oak_functions/native_sdk/native_sdk.h"

#include <cstddef>
#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/oak_functions/native_sdk/native_sdk_ffi.h"

namespace oak::functions::sdk {

// These functions are implemented in Rust, but called from C.
// This code does not take ownership of the raw pointers resulting from the Rust
// callbacks.

extern "C" {

const uint8_t* (*read_request_callback)(size_t* len);
bool (*write_response_callback)(const uint8_t* data, size_t len);
bool (*log_callback)(const uint8_t* data, size_t len);
const uint8_t* (*storage_get_item_callback)(const uint8_t* key, size_t key_len,
                                            size_t* item_len);
const uint8_t* (*read_error_callback)(uint32_t* status_code, size_t* len);

}  // extern "C"

namespace {

// Read the status code and message from the Rust side.  This should be called
// after calling one of the callbacks to get a proper Status.
absl::Status read_status() {
  uint32_t status_code;
  size_t len;
  const char* message =
      reinterpret_cast<const char*>(read_error_callback(&status_code, &len));
  return absl::Status(static_cast<absl::StatusCode>(status_code),
                      absl::string_view(message, len));
}

}  // namespace

absl::StatusOr<std::string> read_request() {
  size_t len;
  const uint8_t* request = read_request_callback(&len);
  if (request == nullptr) {
    return read_status();
  }
  std::string ret(reinterpret_cast<const char*>(request), len);
  return ret;
}

absl::Status write_response(absl::string_view response) {
  if (!write_response_callback(
          reinterpret_cast<const uint8_t*>(response.data()), response.size())) {
    return read_status();
  }
  return absl::OkStatus();
}

absl::Status log(absl::string_view message) {
  if (!log_callback(reinterpret_cast<const uint8_t*>(message.data()),
                    message.size())) {
    return read_status();
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> storage_get_item(absl::string_view key) {
  size_t item_len;
  const uint8_t* item = storage_get_item_callback(
      reinterpret_cast<const uint8_t*>(key.data()), key.size(), &item_len);
  if (item == nullptr) {
    return read_status();
  }
  std::string ret(reinterpret_cast<const char*>(item), item_len);
  return ret;
}

extern "C" void register_callbacks(
    const uint8_t* (*read_request_cb)(size_t* len),
    bool (*write_response_cb)(const uint8_t* data, size_t len),
    bool (*log_cb)(const uint8_t* data, size_t len),
    const uint8_t* (*storage_get_item_cb)(const uint8_t* key, size_t key_len,
                                          size_t* item_len),
    const uint8_t* (*read_error_cb)(uint32_t* status_code, size_t* len)) {
  read_request_callback = read_request_cb;
  write_response_callback = write_response_cb;
  log_callback = log_cb;
  storage_get_item_callback = storage_get_item_cb;
  read_error_callback = read_error_cb;
}

}  // namespace oak::functions::sdk
