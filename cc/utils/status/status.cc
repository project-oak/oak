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

#include "cc/utils/status/status.h"

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"

namespace oak::util::status {

absl::Status Annotate(const absl::Status& s, absl::string_view msg) {
  if (s.ok() || msg.empty()) return s;

  std::string new_msg = absl::Substitute("$0: $1", msg, s.message());
  return absl::Status(s.code(), new_msg);
}

}  // namespace oak::util::status
