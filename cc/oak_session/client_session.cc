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

#include "cc/oak_session/client_session.h"

#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/oak_session_bindings.h"
#include "proto/session/session.pb.h"

namespace oak::session {

namespace {}  // namespace

absl::StatusOr<std::unique_ptr<ClientSession>> ClientSession::Create() {
  const bindings::ErrorOrClientSession result = bindings::new_client_session();

  if (result.error != nullptr) {
    return ErrorIntoStatus(result.error);
  }

  return absl::WrapUnique(new ClientSession(result.result));
}

bool ClientSession::IsOpen() { return bindings::client_is_open(rust_session_); }

absl::Status ClientSession::PutIncomingMessage(
    const v1::SessionResponse& response) {
  const std::string response_bytes = response.SerializeAsString();
  bindings::Error* error = bindings::client_put_incoming_message(
      rust_session_, bindings::BytesFromString(response_bytes));
  return ErrorIntoStatus(error);
}

absl::StatusOr<std::optional<v1::SessionRequest>>
ClientSession::GetOutgoingMessage() {
  const bindings::ErrorOrBytes result =
      bindings::client_get_outgoing_message(rust_session_);
  if (result.error != nullptr) {
    return ErrorIntoStatus(result.error);
  }

  if (result.result == nullptr) {
    return std::nullopt;
  }

  v1::SessionRequest request;
  if (!request.ParseFromString(BytesToString(*result.result))) {
    return absl::InternalError(
        "Failed to parse GetoutoingMessage result bytes as SessionRequest");
  }

  free_bytes(result.result);
  return request;
}

absl::Status ClientSession::Write(
    const v1::PlaintextMessage& unencrypted_request) {
  bindings::Error* error = bindings::client_write(
      rust_session_,
      bindings::BytesFromString(unencrypted_request.SerializeAsString()));

  return ErrorIntoStatus(error);
}

absl::StatusOr<std::optional<v1::PlaintextMessage>> ClientSession::Read() {
  const bindings::ErrorOrBytes result = bindings::client_read(rust_session_);
  if (result.error != nullptr) {
    return ErrorIntoStatus(result.error);
  }

  if (result.result == nullptr) {
    return std::nullopt;
  }

  v1::PlaintextMessage plaintext_message_result;
  if (!plaintext_message_result.ParseFromString(
          bindings::BytesToString(*result.result))) {
    return absl::InternalError(
        "Failed to parse client_read result bytes as PlaintextMessage");
  }

  bindings::free_bytes(result.result);
  return plaintext_message_result;
}

ClientSession::~ClientSession() {
  bindings::free_client_session(rust_session_);
}

}  // namespace oak::session
