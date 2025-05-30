/*
 * Copyright 2025 The Project Oak Authors
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

#include <cstdint>

#include "absl/status/status.h"
#include "cc/ffi/bytes_view.h"
namespace oak::ffi {

extern "C" {
uint32_t absl_status_code(const absl::Status* absl_status);
bindings::BytesView absl_status_message(const absl::Status* absl_status);
void free_absl_status(const absl::Status* absl_status);
}
}  // namespace oak::ffi
