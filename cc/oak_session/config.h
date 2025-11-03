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

#include <utility>

#include "absl/strings/string_view.h"
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

// Simple wrapper to hold on to the SessionConfig pointer to ensure safe(r)
// usage.
//
// Semantically this is close to `std::unique_ptr`, but we can't use
// `unique_ptr` here because (a) we don't want arbitrary callers to be able to
// `release()` the pointer and (b) the memory needs to be released on the Rust
// side.
//
// C++ doesn't have something resembling Rust's "movable only once" semantics;
// C++ move semantics demand that the original value is left in a valid state.
// For us (like `unique_ptr`) the only sensible value is `nullptr`, with runtime
// checks (as unfortunately we can't make the compiler yell at you if you move
// things twice).
class SessionConfigHolder {
 public:
  SessionConfigHolder(const SessionConfigHolder&) = delete;
  SessionConfigHolder& operator=(const SessionConfigHolder&) = delete;
  SessionConfigHolder(SessionConfigHolder&& other) : config_(other.release()) {}
  SessionConfigHolder& operator=(SessionConfigHolder&& other) {
    config_ = other.release();
    return *this;
  }

  ~SessionConfigHolder() {
    if (config_ != nullptr) {
      session_config_free(config_);
    }
  }

  // Relinquishes the ownership of the underlying raw pointer to the caller.
  //
  // WARNING: this pointer will to memory allocated on the Rust side via FFI, so
  // you can't use the usual C++ methods (`delete`, `unique_ptr`, `free`, etc)
  // to release the memory! You *must* pass the pointer back to the Rust side
  // for proper deallocation.
  SessionConfig* release() { return std::exchange(config_, nullptr); }

 private:
  explicit SessionConfigHolder(SessionConfig* config) : config_(config) {}

  SessionConfig* config_;

  // The builder of SessionConfigHolder. Nobody else should be able
  // to construct a holder.
  friend class SessionConfigBuilder;
};

// Convenience wrapper around the SessionConfigBuilder in
// oak_session/src/config.rs. All functionality may not be available, and will
// be added on an as-needed basis.
class SessionConfigBuilder {
 public:
  SessionConfigBuilder(AttestationType attestation_type,
                       HandshakeType handshake_type);
  SessionConfig* Build();
  SessionConfigHolder BuildHolder();

  SessionConfigBuilder AddSelfAttester(absl::string_view attester_id,
                                       bindings::FfiAttester attester);
  SessionConfigBuilder AddSelfEndorser(absl::string_view endorser_id,
                                       bindings::FfiEndorser attester);
  SessionConfigBuilder AddPeerVerifier(
      absl::string_view attester_id, bindings::FfiAttestationVerifier attester);
  SessionConfigBuilder AddSessionBinder(absl::string_view attester_id,
                                        bindings::SigningKey* binding_key);
  SessionConfigBuilder SetSelfStaticPrivateKey(
      bindings::IdentityKey* signing_key);
  SessionConfigBuilder SetPeerStaticPublicKey(absl::string_view public_key);

 private:
  bindings::SessionConfigBuilder* builder_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_CONFIG_H_
