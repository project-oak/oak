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

#include "cc/oak_session/server_session.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/oak_session_bindings.h"
#include "proto/session/session.pb.h"

namespace oak::session {

absl::StatusOr<std::unique_ptr<ServerSession>> ServerSession::Create() {
  bindings::ErrorOrServerSession result = bindings::new_server_session();

  if (result.error != nullptr) {
    return bindings::ErrorIntoStatus(result.error);
  }

  return absl::WrapUnique(new ServerSession(result.result));
}

bool ServerSession::IsOpen() { return bindings::server_is_open(rust_session_); }

absl::Status ServerSession::PutIncomingMessage(
    const v1::SessionRequest& request) {
  std::string request_bytes = request.SerializeAsString();
  bindings::Error* error = bindings::server_put_incoming_message(
      rust_session_, bindings::BytesFromString(request_bytes));
  return bindings::ErrorIntoStatus(error);
}

absl::StatusOr<std::optional<v1::SessionResponse>>
ServerSession::GetOutgoingMessage() {
  bindings::ErrorOrBytes result =
      bindings::server_get_outgoing_message(rust_session_);
  if (result.error != nullptr) {
    return bindings::ErrorIntoStatus(result.error);
  }

  if (result.result == nullptr) {
    return std::nullopt;
  }

  v1::SessionResponse response;
  if (!response.ParseFromString(BytesToString(*result.result))) {
    return absl::InternalError(
        "Failed to parse GetOutoingMessage result bytes as SessionResponse");
  }

  free_bytes(result.result);
  return response;
}

absl::Status ServerSession::Write(absl::string_view unencrypted_request) {
  bindings::Error* error = bindings::server_write(
      rust_session_, bindings::BytesFromString(unencrypted_request));

  return bindings::ErrorIntoStatus(error);
}

absl::StatusOr<std::optional<std::string>> ServerSession::Read() {
  bindings::ErrorOrBytes result = bindings::server_read(rust_session_);
  if (result.error != nullptr) {
    return bindings::ErrorIntoStatus(result.error);
  }

  if (result.result == nullptr) {
    return std::nullopt;
  }

  // Copy into new result string so we can free the bytes.
  std::string result_string = BytesToString(*result.result);

  bindings::free_bytes(result.result);
  return result_string;
}

ServerSession::~ServerSession() {
  bindings::free_server_session(rust_session_);
}

}  // namespace oak::session
