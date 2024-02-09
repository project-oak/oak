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

#ifndef THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_H_
#define THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

// We call oak_main without arguments, and oak_main then calls read_request,
// processes the request, and then calls write_response.  This makes the API
// compatible with Oak Functions.
#define OAK_MAIN void oak_main()

namespace oak::functions::sdk {

absl::StatusOr<std::string> read_request();
absl::Status write_response(absl::string_view response);
absl::Status log(absl::string_view message);
absl::StatusOr<std::string> storage_get_item(absl::string_view key);

}  // namespace oak::functions::sdk


#endif  // THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_H_
