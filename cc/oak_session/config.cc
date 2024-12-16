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

#include "cc/oak_session/config.h"

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "cc/oak_session/oak_session_bindings.h"

namespace oak::session {
SessionConfigBuilder::SessionConfigBuilder(AttestationType attestation_type,
                                           HandshakeType handshake_type) {
  bindings::ErrorOrSessionConfigBuilder builder_result =
      bindings::new_session_config_builder(static_cast<int>(attestation_type),
                                           static_cast<int>(handshake_type));

  // The configuration enums should be properly set up to match the valid rust
  // values. If an error is returned from the underlying implementation, then we
  // have an implementation error here that should be fixed.
  // So this error is fatal, rather than propagating.
  if (builder_result.error != nullptr) {
    LOG(FATAL) << absl::StrCat(
        "Failed to create builder: ",
        bindings::BytesToString(builder_result.error->message));
  }

  builder_ = builder_result.result;
}

session::SessionConfig* SessionConfigBuilder::Build() {
  return bindings::session_config_builder_build(builder_);
}

}  // namespace oak::session
