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

#include "cc/oak_session/oak_session_bindings.h"

#include <string>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"

namespace oak::session::bindings {

BytesView::BytesView(absl::string_view bytes)
    : data(bytes.data()), len(bytes.size()) {}

BytesView::BytesView(RustBytes bytes) : data(bytes.data), len(bytes.len) {}

std::ostream& operator<<(std::ostream& stream, const BytesView& bytes) {
  stream << absl::string_view(bytes.data, bytes.len);
  return stream;
}

absl::Status ErrorIntoStatus(bindings::Error* error) {
  if (error == nullptr) {
    return absl::OkStatus();
  }
  absl::Status status =
      absl::Status(absl::StatusCode::kInternal, error->message);
  free_error(error);
  return status;
}

}  // namespace oak::session::bindings
