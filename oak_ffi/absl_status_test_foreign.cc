//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#include "absl/log/die_if_null.h"
#include "absl/status/status.h"
#include "cc/ffi/absl_status.h"
#include "cc/ffi/bytes_view.h"

// A simple test function to test returning CxxString to Rust.
extern "C" {
absl::Status* create_ok_status() {
  absl::Status ok;
  return ABSL_DIE_IF_NULL(new absl::Status(ok));
}

absl::Status* create_internal_error(oak::ffi::bindings::BytesView msg) {
  absl::Status err = absl::InternalError(msg);
  return ABSL_DIE_IF_NULL(new absl::Status(err));
}
}
