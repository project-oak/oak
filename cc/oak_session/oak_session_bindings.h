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

#ifndef CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_
#define CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_

#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "cc/oak_session/oak_session_bindings.h"

namespace oak::session::bindings {

// These correspond to the definitions in oak_session/ffi/config.rs
constexpr int HANDSHAKE_TYPE_NOISE_KK = 1;
constexpr int HANDSHAKE_TYPE_NOISE_KN = 2;
constexpr int HANDSHAKE_TYPE_NOISE_NK = 3;
constexpr int HANDSHAKE_TYPE_NOISE_NN = 4;

// These correspond to the definitions in oak_session/ffi/config.rs
constexpr int ATTESTATION_TYPE_BIDIRECTIONAL = 1;
constexpr int ATTESTATION_TYPE_SELF_UNIDIRECTIONAL = 2;
constexpr int ATTESTATION_TYPE_PEER_UNIDIRECTIONAL = 3;
constexpr int ATTESTATION_TYPE_UNATTESTED = 4;

// The corresponding C definitions for the Rust FFI bindings.
// The rust bindings are defined in: oak_session/ffi

// An opaque Rust SessionConfigBuilder.
class SessionConfigBuilder;

// An opaque Rust SessionConfig pointer.
class SessionConfig;

// An opaque Rust ServerSession.
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
class ServerSession;

// An opaque Rust ClientSession.
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
class ClientSession;

// An opaque Rust Attestor
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
class FfiAttester {
  void* attester;
};

// An opaque Rust Endorser
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
class FfiEndorser {
  void* endorser;
};

// An opaque Rust Attestation Verifier
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
class FfiAttestationVerifier {
  void* verifier;
};

// A struct holding a sequence of Bytes allocated in Rust.
// Corresponds to RustBytes struct in oak_session/ffi/types.rs
//
// C/C++ that receives an instance of this as a return value from Rust will be
// expected to free it, either by calling `free_rust_bytes_contents`, or by
// passing the bytes back to Rust as an argument to a function that specifies in
// the documentation that it will re-claim ownership of the parameter.
struct RustBytes {
  const char* data;
  uint64_t len;

  operator absl::string_view() { return absl::string_view(data, len); }
};

// A borrowed view of bytes from either C or Rust.
//
// Functions that use or return BytesView structures should document the
// lifetime expectations of the view.
//
// Corresponds to BytesView struct in oak_session/ffi/types.rs
struct BytesView {
  const char* data;
  uint64_t len;

  explicit BytesView(absl::string_view data);
  explicit BytesView(RustBytes data);
};

// Corresponds to Error struct in oak_session/ffi/types.rs
struct Error {
  RustBytes message;
};

// Corresponds to ErrorOrBytes struct in oak_session/ffi/types.rs
struct ErrorOrRustBytes {
  RustBytes* result;
  Error* error;
};

// Corresponds to ErrorOrClientSession struct in
// oak_session/ffi/client_session.rs
struct ErrorOrClientSession {
  ClientSession* result;
  Error* error;
};

// Corresponds to ErrorOrServerSession struct in
// oak_session/ffi/server_session.rs
struct ErrorOrServerSession {
  ServerSession* result;
  Error* error;
};

// Corresponds to ErrorOrSessionConfigBuilder struct in
// oak_session/ffi/config.rs
struct ErrorOrSessionConfigBuilder {
  SessionConfigBuilder* result;
  Error* error;
};

// Corresponds to ErrorOrFfiAttester struct in
// oak_session/ffi/attestation.rs
struct ErrorOrFfiAttester {
  FfiAttester result;
  Error* error;
};

// Corresponds to ErrorOrFfiEndorser struct in
// oak_session/ffi/attestation.rs
struct ErrorOrFfiEndorser {
  FfiEndorser result;
  Error* error;
};

struct SigningKey;

extern "C" {

// Corresponds to functions in oak_session/ffi/config.rs
extern ErrorOrSessionConfigBuilder new_session_config_builder(uint32_t,
                                                              uint32_t);
extern SessionConfigBuilder* session_config_builder_add_self_attester(
    SessionConfigBuilder*, BytesView, FfiAttester);
extern SessionConfigBuilder* session_config_builder_add_self_endorser(
    SessionConfigBuilder*, BytesView, FfiEndorser);
extern SessionConfigBuilder* session_config_builder_add_peer_verifier(
    SessionConfigBuilder*, BytesView, FfiAttestationVerifier);
extern SessionConfigBuilder* session_config_builder_add_session_binder(
    SessionConfigBuilder*, BytesView, SigningKey*);
extern RustBytes new_fake_evidence(BytesView, BytesView);
extern ErrorOrFfiAttester new_simple_attester(BytesView);
extern RustBytes new_fake_endorsements(BytesView);
extern ErrorOrFfiEndorser new_simple_endorser(BytesView);
extern FfiAttestationVerifier new_fake_attestation_verifier(BytesView,
                                                            BytesView);
extern SigningKey* new_random_signing_key();
extern RustBytes signing_key_verifying_key_bytes(SigningKey*);
extern void free_signing_key(SigningKey*);

extern SessionConfig* session_config_builder_build(SessionConfigBuilder*);

// Corresponds to functions in oak_session/ffi/client_session.rs
extern ErrorOrClientSession new_client_session(SessionConfig*);
extern bool client_is_open(ClientSession*);
extern Error* client_put_incoming_message(ClientSession*, BytesView);
extern ErrorOrRustBytes client_get_outgoing_message(ClientSession*);
extern ErrorOrRustBytes client_read(ClientSession*);
extern Error* client_write(ClientSession*, BytesView);
extern void free_client_session(ClientSession*);

// Corresponds to functions in oak_session/ffi/server_session.rs
extern ErrorOrServerSession new_server_session(SessionConfig*);
extern bool server_is_open(ServerSession*);
extern Error* server_put_incoming_message(ServerSession*, BytesView);
extern ErrorOrRustBytes server_get_outgoing_message(ServerSession*);
extern ErrorOrRustBytes server_read(ServerSession*);
extern Error* server_write(ServerSession*, BytesView);
extern void free_server_session(ServerSession*);

// Corresponds to functions in oak_session/ffi/types.rs
extern void free_rust_bytes(RustBytes*);
extern void free_rust_bytes_contents(RustBytes);
extern void free_error(Error*);
}

// A convenience function to create a new absl::Status instance containing a
// message populated from the provided error.
//
// The error will be released.
absl::Status ErrorIntoStatus(bindings::Error* error);

}  // namespace oak::session::bindings

#endif  // CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_
