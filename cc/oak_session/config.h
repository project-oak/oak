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

#include <optional>
#include <string>

#include "cc/oak_session/oak_session_bindings.h"

#ifndef CC_OAK_SESSION_CONFIG_H_
#define CC_OAK_SESSION_CONFIG_H_

namespace oak::session {

// These correspond to the values is oak_session/src/attestation.rs.
enum class AttestationType {
  kBidirectional = bindings::ATTESTATION_TYPE_BIDIRECTIONAL,
  kSelfUnidirectional = bindings::ATTESTATION_TYPE_SELF_UNIDIRECTIONAL,
  kPeerUnidirectional = bindings::ATTESTATION_TYPE_PEER_UNIDIRECTIONAL,
  kUnattested = bindings::ATTESTATION_TYPE_UNATTESTED,
};

// These correspond to the values is oak_session/src/handshake.rs.
enum class HandshakeType {
  kNoiseKK = bindings::HANDSHAKE_TYPE_NOISE_KK,
  kNoiseKN = bindings::HANDSHAKE_TYPE_NOISE_KN,
  kNoiseNK = bindings::HANDSHAKE_TYPE_NOISE_NK,
  kNoiseNN = bindings::HANDSHAKE_TYPE_NOISE_NN,
};

// An opaque pointer to a Rust SessionConfig that can be used for constructing
// sessions.
using SessionConfig = bindings::SessionConfig;

// Convenience wrapper around the SessionConfigBuilder in
// oak_session/src/config.rs. All functionality may not be available, and will
// be added on an as-needed basis.
class SessionConfigBuilder {
 public:
  SessionConfigBuilder(AttestationType attestation_type,
                       HandshakeType handshake_type);
  SessionConfig* Build();

 private:
  bindings::SessionConfigBuilder* builder_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_CONFIG_H_
