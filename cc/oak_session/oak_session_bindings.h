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

// A struct holding a sequence of Bytes.
// Corresponds to Bytes struct in oak_session/ffi/types.rs
struct Bytes {
  const char* data;
  uint64_t len;
};

// Create a `Bytes` instance wrapping the provided string data.
// The lifetime of the created bytes is determined by the lifetime
// of the data backing the string_view.
Bytes BytesFromString(absl::string_view bytes);

// Create a new string wrapping the Bytes object.
// The Bytes data will be copied into a new string.
std::string BytesToString(Bytes bytes);

// Corresponds to Error struct in oak_session/ffi/types.rs
struct Error {
  Bytes message;
};

// Corresponds to ErrorOrBytes struct in oak_session/ffi/types.rs
struct ErrorOrBytes {
  Bytes* result;
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

extern "C" {

// Corresponds to functions in oak_session/ffi/config.rs
extern ErrorOrSessionConfigBuilder new_session_config_builder(uint32_t,
                                                              uint32_t);
extern SessionConfig* session_config_builder_build(SessionConfigBuilder*);

// Corresponds to functions in oak_session/ffi/client_session.rs
extern ErrorOrClientSession new_client_session(SessionConfig*);
extern bool client_is_open(ClientSession*);
extern Error* client_put_incoming_message(ClientSession*, Bytes);
extern ErrorOrBytes client_get_outgoing_message(ClientSession*);
extern ErrorOrBytes client_read(ClientSession*);
extern Error* client_write(ClientSession*, Bytes);
extern void free_client_session(ClientSession*);

// Corresponds to functions in oak_session/ffi/server_session.rs
extern ErrorOrServerSession new_server_session(SessionConfig*);
extern bool server_is_open(ServerSession*);
extern Error* server_put_incoming_message(ServerSession*, Bytes);
extern ErrorOrBytes server_get_outgoing_message(ServerSession*);
extern ErrorOrBytes server_read(ServerSession*);
extern Error* server_write(ServerSession*, Bytes);
extern void free_server_session(ServerSession*);

// Corresponds to functions in oak_session/ffi/types.rs
extern void free_bytes(Bytes*);
extern void free_error(Error*);
}

// A convenience function to create a new absl::Status instance containing a
// message populated from the provided error.
//
// The error will be released.
absl::Status ErrorIntoStatus(bindings::Error* error);

}  // namespace oak::session::bindings

#endif  // CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_
