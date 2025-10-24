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

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
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

absl::string_view CertificateBasedAttestationId();
absl::string_view ConfidentialSpaceAttestationId();

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

// A class for managing the underlying `SessionConfigBuilder` Rust
// bytes. This wrapper takes care of managing and cleaning up the underlying
// Rust bytes.
//
// As with `SessionConfigHolder`, semantically this is close to
// `std::unique_ptr`.
class SessionConfigBuilderHolder {
 public:
  explicit SessionConfigBuilderHolder(bindings::SessionConfigBuilder* builder)
      : builder_(builder) {}

  SessionConfigBuilderHolder() : builder_(nullptr) {}

  // `SessionConfigBuilderHolder` is not copyable.
  SessionConfigBuilderHolder(const SessionConfigBuilderHolder&) = delete;
  SessionConfigBuilderHolder& operator=(const SessionConfigBuilderHolder&) =
      delete;

  // Release the builder_ of the moved object
  SessionConfigBuilderHolder(SessionConfigBuilderHolder&& other)
      : builder_(other.release()) {};

  SessionConfigBuilderHolder& operator=(SessionConfigBuilderHolder&& other) {
    if (this == &other) return *this;
    if (builder_ != nullptr) bindings::free_session_config_builder(builder_);
    builder_ = other.release();
    return *this;
  }

  // Return true if the `SessionConfigBuilderHolder` posseses a non-null
  // pointer.
  explicit operator bool() const { return builder_ != nullptr; }

  ~SessionConfigBuilderHolder() {
    // Do not delete the builder_ in the event that it is null. This can occur
    // from the bytes being released or moved elsewhere.
    if (builder_ != nullptr) {
      bindings::free_session_config_builder(builder_);
      builder_ = nullptr;
    }
  }

  // Fetch the underlying builder_ while having the class still maintain
  // owernership of the bytes.
  bindings::SessionConfigBuilder* const get() { return builder_; }

  // Release ownership of the underlying builder_. If release() has been called
  // previously or if its contents have been been moved, this will return a
  // nullptr. Calling this method should be done so carefully as it is very
  // likely to cause a memory leak.
  bindings::SessionConfigBuilder* release() {
    bindings::SessionConfigBuilder* result = builder_;
    builder_ = nullptr;
    return result;
  }

 private:
  bindings::SessionConfigBuilder* builder_;
};

// Convenience wrapper around the SessionConfigBuilder in
// oak_session/src/config.rs. All functionality may not be available, and will
// be added on an as-needed basis.
//
// Once `Build` has been called on an instance, the underlying builder will no
// longer be valid. If you continue to try to use the builder, the `Add`
// operations will be no-ops, and the `Build` operation will return a null
// pointer.
class SessionConfigBuilder {
 public:
  SessionConfigBuilder(AttestationType attestation_type,
                       HandshakeType handshake_type);
  ~SessionConfigBuilder() = default;
  SessionConfig* Build();
  SessionConfigHolder BuildHolder();

  SessionConfigBuilder(const SessionConfigBuilder&) = delete;
  SessionConfigBuilder& operator=(const SessionConfigBuilder&) = delete;
  SessionConfigBuilder(SessionConfigBuilder&& other) {
    builder_ = std::move(other.builder_);
  }
  SessionConfigBuilder& operator=(SessionConfigBuilder&& other) {
    builder_ = std::move(other.builder_);
    return *this;
  }

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

  // Allows direct manipulation of the underlying
  // `bindings::SessionConfigBuilder*`.
  //
  // Ownership of the `SessionConfigBuilder` pointer is passed to `update_fn`,
  // and we take the ownership of the returned `SessionConfigBuilder`. If the
  // `update_fn` returns an error, it is responsible for releasing the memory.
  // Any errors that `update_fn` returns are propagated to the caller.
  //
  // If at all possbile do not use this method due to the sharp edges and prefer
  // to implement proper wrappers for the FFI calls.
  absl::Status UpdateRaw(
      absl::AnyInvocable<absl::StatusOr<SessionConfigBuilderHolder>(
          SessionConfigBuilderHolder)>
          update_fn);

 private:
  SessionConfigBuilderHolder builder_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_CONFIG_H_
