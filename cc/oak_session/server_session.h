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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/rust_bytes.h"
#include "cc/oak_session/config.h"
#include "proto/attestation/verification.pb.h"
#include "proto/session/session.pb.h"

#ifndef CC_OAK_SESSION_SERVER_SESSION_H_
#define CC_OAK_SESSION_SERVER_SESSION_H_

namespace oak::session {

// A C++ wrapper around FFI bindings to a Rust ClientSession instance.
//
// This class exposes the functionality of the `ProtocolEngine` and `Session`
// traits for the instance.
//
// See oak_session/session.rs for more info.
class ServerSession {
 public:
  // A valid `SessionConfig` can be obtained using
  // oak::session::SessionConfigBuilder.
  ABSL_DEPRECATED("Use the overload accepting SessionConfigHolder.")
  static absl::StatusOr<std::unique_ptr<ServerSession>> Create(
      session::SessionConfig* config);
  static absl::StatusOr<std::unique_ptr<ServerSession>> Create(
      session::SessionConfigHolder config);
  // Use a default configuration, Unattested + NoiseNN
  ABSL_DEPRECATED("Use the config-providing variant.")
  static absl::StatusOr<std::unique_ptr<ServerSession>> Create();
  ~ServerSession();

  bool IsOpen();
  absl::Status PutIncomingMessage(const v1::SessionRequest& request);
  absl::StatusOr<std::optional<v1::SessionResponse>> GetOutgoingMessage();
  ABSL_DEPRECATED(
      "Use the version accepting an absl::string_view to avoid needless "
      "copying.")
  absl::Status Write(const v1::PlaintextMessage& unencrypted_request);
  ABSL_DEPRECATED("Use ReadToRustBytes instead to avoid needless copying.")
  absl::StatusOr<std::optional<v1::PlaintextMessage>> Read();
  absl::Status Write(absl::string_view unencrypted_request);

  // This returns a wrapper around the Rust bytes generated from the library. It
  // can be cast to an absl::string_view for read-only usage, otherwise it
  // should be copied (for example, by creating a std::string from it.)
  absl::StatusOr<std::optional<ffi::RustBytes>> ReadToRustBytes();

  // Returns a unique `SessionBindingToken` for this session.
  //
  // This token can be used by the application to bind other data or
  // operations to the security properties (authentication, encryption)
  // of this specific session. `info_string` allows for domain separation
  // if multiple tokens are needed for different purposes within the same
  // session.
  //
  // This method can only be called successfully when `IsOpen()` is true.
  absl::StatusOr<ffi::RustBytes> GetSessionBindingToken(absl::string_view info);

  // Retrieves the peer's attestation evidence.
  //
  // Returns a `oak::attestation::v1::CollectedAttestation` proto containing
  // the evidence, or an error status if the operation fails (e.g., session
  // not open, FFI error, or deserialization failure).
  absl::StatusOr<oak::attestation::v1::CollectedAttestation>
  GetPeerAttestationEvidence();

 private:
  explicit ServerSession(bindings::ServerSession* rust_session)
      : rust_session_(rust_session) {}
  bindings::ServerSession* rust_session_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_SERVER_SESSION_H_
