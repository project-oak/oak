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

#include <utility>

#include "absl/functional/any_invocable.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/bytes_view.h"
#include "cc/oak_session/oak_session_bindings.h"

namespace oak::session {

absl::string_view CertificateBasedAttestationId() {
  return absl::string_view(bindings::certificate_based_attestation_id());
}

absl::string_view ConfidentialSpaceAttestationId() {
  return absl::string_view(bindings::confidential_space_attestation_id());
}

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
        static_cast<absl::string_view>(builder_result.error->message));
  }

  builder_ = SessionConfigBuilderHolder(builder_result.result);
}

SessionConfigBuilder SessionConfigBuilder::AddSelfAttester(
    absl::string_view attester_id, bindings::FfiAttester attester) {
  if (builder_) {
    builder_ =
        SessionConfigBuilderHolder(session_config_builder_add_self_attester(
            builder_.release(), ffi::bindings::BytesView(attester_id),
            attester));
  }
  return std::move(*this);
}

SessionConfigBuilder SessionConfigBuilder::AddSelfEndorser(
    absl::string_view endorser_id, bindings::FfiEndorser endorser) {
  if (builder_) {
    builder_ =
        SessionConfigBuilderHolder(session_config_builder_add_self_endorser(
            builder_.release(), ffi::bindings::BytesView(endorser_id),
            endorser));
  }
  return std::move(*this);
}

SessionConfigBuilder SessionConfigBuilder::AddPeerVerifier(
    absl::string_view attester_id, bindings::FfiAttestationVerifier verifier) {
  if (builder_) {
    builder_ =
        SessionConfigBuilderHolder(session_config_builder_add_peer_verifier(
            builder_.release(), ffi::bindings::BytesView(attester_id),
            verifier));
  }
  return std::move(*this);
}

SessionConfigBuilder SessionConfigBuilder::AddSessionBinder(
    absl::string_view attester_id, bindings::SigningKey* binding_key) {
  if (builder_) {
    builder_ =
        SessionConfigBuilderHolder(session_config_builder_add_session_binder(
            builder_.release(), ffi::bindings::BytesView(attester_id),
            binding_key));
  }
  return std::move(*this);
}

SessionConfigBuilder SessionConfigBuilder::SetSelfStaticPrivateKey(
    bindings::IdentityKey* signing_key) {
  if (builder_) {
    builder_ = SessionConfigBuilderHolder(
        session_config_builder_set_self_static_private_key(builder_.release(),
                                                           signing_key));
  }
  return std::move(*this);
}

SessionConfigBuilder SessionConfigBuilder::SetPeerStaticPublicKey(
    absl::string_view public_key) {
  if (builder_) {
    builder_ = SessionConfigBuilderHolder(
        session_config_builder_set_peer_static_public_key(
            builder_.release(), ffi::bindings::BytesView(public_key)));
  }
  return std::move(*this);
}

session::SessionConfig* SessionConfigBuilder::Build() {
  if (!builder_) {
    return nullptr;
  }
  return bindings::session_config_builder_build(builder_.release());
}

absl::Status SessionConfigBuilder::UpdateRaw(
    absl::AnyInvocable<
        absl::StatusOr<SessionConfigBuilderHolder>(SessionConfigBuilderHolder)>
        update_fn) {
  if (!builder_) {
    return absl::FailedPreconditionError("Builder is already built.");
  }
  auto result = update_fn(std::move(builder_));
  if (!result.ok()) {
    return result.status();
  }
  builder_ = std::move(*result);
  return absl::OkStatus();
}

session::SessionConfigHolder SessionConfigBuilder::BuildHolder() {
  return SessionConfigHolder(Build());
}

}  // namespace oak::session
