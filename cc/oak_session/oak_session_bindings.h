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
#include "cc/ffi/bytes_bindings.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/error_bindings.h"
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
struct FfiAttester {
  void* attester;
};

// An opaque Rust Endorser
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
struct FfiEndorser {
  void* endorser;
};

// An opaque Rust Attestation Verifier
// Pointers to this incomplete type are used to reference
// the corresponding Rust struct in the function calls.
struct FfiAttestationVerifier {
  void* verifier;
};

// Corresponds to ErrorOrClientSession struct in
// oak_session/ffi/client_session.rs
struct ErrorOrClientSession {
  ClientSession* result;
  ffi::bindings::Error* error;
};

// Corresponds to ErrorOrServerSession struct in
// oak_session/ffi/server_session.rs
struct ErrorOrServerSession {
  ServerSession* result;
  ffi::bindings::Error* error;
};

// Corresponds to ErrorOrSessionConfigBuilder struct in
// oak_session/ffi/config.rs
struct ErrorOrSessionConfigBuilder {
  SessionConfigBuilder* result;
  ffi::bindings::Error* error;
};

// Corresponds to ErrorOrFfiAttester struct in
// oak_session/ffi/attestation.rs
struct ErrorOrFfiAttester {
  FfiAttester result;
  ffi::bindings::Error* error;
};

// Corresponds to ErrorOrFfiEndorser struct in
// oak_session/ffi/attestation.rs
struct ErrorOrFfiEndorser {
  FfiEndorser result;
  ffi::bindings::Error* error;
};

struct SigningKey;
struct IdentityKey;

struct ErrorOrIdentityKey {
  IdentityKey* result;
  ffi::bindings::Error* error;
};

extern "C" {
// Corresponds to functions in oak_session/ffi/config.rs
extern const char* const certificate_based_attestation_id();
extern const char* const confidential_space_attestation_id();
extern ErrorOrSessionConfigBuilder new_session_config_builder(uint32_t,
                                                              uint32_t);
extern SessionConfigBuilder* session_config_builder_add_self_attester(
    SessionConfigBuilder*, ffi::bindings::BytesView, FfiAttester);
extern SessionConfigBuilder* session_config_builder_add_self_endorser(
    SessionConfigBuilder*, ffi::bindings::BytesView, FfiEndorser);
extern SessionConfigBuilder* session_config_builder_add_peer_verifier(
    SessionConfigBuilder*, ffi::bindings::BytesView, FfiAttestationVerifier);
extern SessionConfigBuilder* session_config_builder_add_session_binder(
    SessionConfigBuilder*, ffi::bindings::BytesView, SigningKey*);
extern SessionConfigBuilder* session_config_builder_set_self_static_private_key(
    SessionConfigBuilder*, IdentityKey*);
extern SessionConfigBuilder* session_config_builder_set_peer_static_public_key(
    SessionConfigBuilder*, ffi::bindings::BytesView);
extern ffi::bindings::RustBytes new_fake_evidence(ffi::bindings::BytesView,
                                                  ffi::bindings::BytesView);
extern ErrorOrFfiAttester new_simple_attester(ffi::bindings::BytesView);
extern ffi::bindings::RustBytes new_fake_endorsements(ffi::bindings::BytesView);
extern ErrorOrFfiEndorser new_simple_endorser(ffi::bindings::BytesView);
extern FfiAttestationVerifier new_fake_attestation_verifier(
    ffi::bindings::BytesView, ffi::bindings::BytesView);
extern SigningKey* new_random_signing_key();
extern ffi::bindings::RustBytes signing_key_verifying_key_bytes(SigningKey*);
extern void free_signing_key(SigningKey*);

extern IdentityKey* new_identity_key();
extern ErrorOrIdentityKey new_identity_key_from_bytes(ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes identity_key_get_public_key(
    IdentityKey*);

extern SessionConfig* session_config_builder_build(SessionConfigBuilder*);
extern void session_config_free(SessionConfig*);

// Corresponds to functions in oak_session/ffi/client_session.rs
extern ErrorOrClientSession new_client_session(SessionConfig*);
extern bool client_is_open(ClientSession*);
extern ffi::bindings::Error* client_put_incoming_message(
    ClientSession*, ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes client_get_outgoing_message(
    ClientSession*);
extern ffi::bindings::ErrorOrRustBytes client_read(ClientSession*);
extern ffi::bindings::Error* client_write(ClientSession*,
                                          ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes client_get_session_binding_token(
    ClientSession*, ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes client_get_peer_attestation_evidence(
    ClientSession*);
extern void free_client_session(ClientSession*);

// Corresponds to functions in oak_session/ffi/server_session.rs
extern ErrorOrServerSession new_server_session(SessionConfig*);
extern bool server_is_open(ServerSession*);
extern ffi::bindings::Error* server_put_incoming_message(
    ServerSession*, ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes server_get_outgoing_message(
    ServerSession*);
extern ffi::bindings::ErrorOrRustBytes server_read(ServerSession*);
extern ffi::bindings::Error* server_write(ServerSession*,
                                          ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes server_get_session_binding_token(
    ServerSession*, ffi::bindings::BytesView);
extern ffi::bindings::ErrorOrRustBytes server_get_peer_attestation_evidence(
    ServerSession*);
extern void free_server_session(ServerSession*);
}

}  // namespace oak::session::bindings

#endif  // CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_
