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

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/oak_session_bindings.h"
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
  static absl::StatusOr<std::unique_ptr<ServerSession>> Create();
  ~ServerSession();

  bool IsOpen();
  absl::Status PutIncomingMessage(const v1::SessionRequest& request);
  absl::StatusOr<std::optional<v1::SessionResponse>> GetOutgoingMessage();
  absl::Status Write(absl::string_view unencrypted_request);
  absl::StatusOr<std::optional<std::string>> Read();

 private:
  ServerSession(bindings::ServerSession* rust_session)
      : rust_session_(rust_session) {}
  bindings::ServerSession* rust_session_;
};

}  // namespace oak::session

#endif  // CC_OAK_SESSION_SERVER_SESSION_H_
