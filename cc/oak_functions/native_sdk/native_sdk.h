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

#ifndef THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_H_
#define THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

// We call oak_main without arguments, and oak_main then calls read_request,
// processes the request, and then calls write_response.  This makes the API
// compatible with Oak Functions.
#define OAK_MAIN extern "C" void oak_main()

namespace oak::functions::sdk {

// Calls the read_request Rust function that reads a request from the client.
absl::StatusOr<std::string> read_request();

// Calls the write_response Rust function that writes a response to the client.
absl::Status write_response(absl::string_view response);

// Calls the log Rust function that writes a debug log message if in debug mode.
absl::Status log(absl::string_view message);

// Calls the lookup_data Rust function that looks up an item from the in-memory
// key/value lookup store.
absl::StatusOr<std::string> storage_get_item(absl::string_view key);

}  // namespace oak::functions::sdk

#endif  // THIRD_PARTY_OAK_CC_OAK_FUNCTIONS_NATIVE_SDK_NATIVE_SDK_H_
