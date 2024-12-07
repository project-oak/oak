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

namespace oak::session::bindings {

// The corresponding C definitions for the Rust FFI bindings.
// The rust bindings are defined in: oak_session/ffi

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

inline Bytes BytesFromString(absl::string_view bytes) {
  return Bytes{.data = bytes.data(), .len = bytes.size()};
}

inline std::string BytesToString(Bytes bytes) {
  return std::string(bytes.data, bytes.len);
}

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

extern "C" {

// Corresponds to functions in oak_session/ffi/client_session.rs
extern ErrorOrClientSession new_client_session();
extern bool client_is_open(ClientSession*);
extern Error* client_put_incoming_message(ClientSession*, Bytes);
extern ErrorOrBytes client_get_outgoing_message(ClientSession*);
extern ErrorOrBytes client_read(ClientSession*);
extern Error* client_write(ClientSession*, Bytes);
extern void free_client_session(ClientSession*);

// Corresponds to functions in oak_session/ffi/server_session.rs
extern ErrorOrServerSession new_server_session();
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
absl::Status ErrorIntoStatus(bindings::Error* error) {
  if (error == nullptr) {
    return absl::OkStatus();
  }
  absl::Status status = absl::Status(absl::StatusCode::kInternal,
                                     bindings::BytesToString(error->message));
  free_error(error);
  return status;
}

}  // namespace oak::session::bindings

#endif  // CC_OAK_SESSION_OAK_SESSION_BINDINGS_H_
