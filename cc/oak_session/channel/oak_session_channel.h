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

#ifndef CC_SERVER_OAK_SESSION_CHANNEL_H_
#define CC_SERVER_OAK_SESSION_CHANNEL_H_

#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "cc/oak_session/rust_bytes.h"
#include "cc/utils/status/status.h"
#include "proto/session/session.pb.h"

namespace oak::session::channel {

// OakSessionChannel manages an established connection between a client and
// server that communicate using the Noise Protocol via an Oak Session.
//
// This parameterized class provides the implementation for channels managed on
// both the client and server sides.
//
// SendMessage is the type that will be sent out on the wire, ReceiveMessage is
// the type that will be coming in on the wire, and Session is the type of the
// underlying oak session that manages the encrypted channel state.
template <typename SendMessage, typename ReceiveMessage, typename Session>
class OakSessionChannel {
 public:
  // Instances of `OakSessionChannel` need an implementation of this interface,
  // which provides the means for receiving requests from a client, and sending
  // responses back to that client.
  class Transport {
   public:
    virtual ~Transport() = default;
    virtual absl::Status Send(SendMessage&& message) = 0;

    // Implementations should block until a new message is available to return.
    // Blocking semantics, deadlines, etc should be defined by the particular
    // implementation.
    virtual absl::StatusOr<ReceiveMessage> Receive() = 0;
  };

  OakSessionChannel(std::unique_ptr<Session> session,
                    std::unique_ptr<Transport> transport)
      : session_(std::move(session)), transport_(std::move(transport)) {}

  // Encrypt and send a message back to the other party.
  absl::Status Send(absl::string_view unencrypted_message) {
    absl::Status write_result = session_->Write(unencrypted_message);
    if (!write_result.ok()) {
      return util::status::Annotate(write_result,
                                    "Failed to write message for encryption");
    }

    absl::StatusOr<std::optional<SendMessage>> outgoing_message =
        session_->GetOutgoingMessage();
    if (!outgoing_message.ok()) {
      return util::status::Annotate(outgoing_message.status(),
                                    "Failed to get encrypted outgoing message");
    }
    if (*outgoing_message == std::nullopt) {
      return absl::InternalError(
          "Reading back encrypted message returned null result");
    }

    absl::Status send_result = transport_->Send(std::move(**outgoing_message));
    if (!send_result.ok()) {
      return util::status::Annotate(
          send_result, "Failed to send outgoing message on provided transport");
    }

    return absl::OkStatus();
  }

  // Receive and decrypt a message from the other party.
  // The call will block until a message is available, as defined by the
  // provided Transport.
  absl::StatusOr<std::string> Receive() {
    absl::StatusOr<ReceiveMessage> next_request = transport_->Receive();

    if (!next_request.ok()) {
      return util::status::Annotate(next_request.status(),
                                    "Failed to receive request from transport");
    }

    absl::Status put_result = session_->PutIncomingMessage(*next_request);

    if (!put_result.ok()) {
      return util::status::Annotate(
          put_result, "Failed to put incoming request onto state machine");
    }

    absl::StatusOr<std::optional<RustBytes>> decrypted_message =
        session_->ReadToRustBytes();

    if (!decrypted_message.ok()) {
      return util::status::Annotate(
          decrypted_message.status(),
          "Failed to read decrypted message from state machine");
    }

    if (*decrypted_message == std::nullopt) {
      return absl::InternalError(
          "Reading back decrypted message from state machine returned null "
          "result");
    }

    return std::string(static_cast<absl::string_view>(**decrypted_message));
  }

  // Create a new OakSessionChannel instance with the provided session and
  // transport.
  //
  // session should be a newly created Session instance with a
  // configuration that matches the configuration of the corresponding client or
  // server on the other side..
  //
  // The call will block during the initialization sequence, and return an open
  // channel that is ready to use, or return an error if the handshake didn't
  // succeed.
  static absl::StatusOr<std::unique_ptr<OakSessionChannel>> Create(
      std::unique_ptr<Session> session, std::unique_ptr<Transport> transport);

 private:
  std::unique_ptr<Session> session_;
  std::unique_ptr<Transport> transport_;
};

}  // namespace oak::session::channel

#endif  // CC_SERVER_OAK_SESSION_CHANNEL_H_
