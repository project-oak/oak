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

#ifndef CC_UTILS_STATUS_H_
#define CC_UTILS_STATUS_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"

namespace oak::util::status {

// Annotate an existing status message by prepending the provided msg.
absl::Status Annotate(const absl::Status& s, absl::string_view msg);

}  // namespace oak::util::status

#endif  // CC_UTILS_STATUS_H_
