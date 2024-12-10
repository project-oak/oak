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

#include "cc/client/session_client.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/client_session.h"
#include "cc/utils/status/status.h"
#include "proto/session/session.pb.h"

namespace oak::client {

absl::StatusOr<std::unique_ptr<OakSessionClient::Channel>>
OakSessionClient::NewChannel(std::unique_ptr<Channel::Transport> transport) {
  absl::StatusOr<std::unique_ptr<session::ClientSession>> session =
      session::ClientSession::Create();

  while (!(*session)->IsOpen()) {
    absl::StatusOr<std::optional<session::v1::SessionRequest>> init_request =
        (*session)->GetOutgoingMessage();
    if (!init_request.ok()) {
      return util::status::Annotate(
          init_request.status(),
          "Failed to get outgoing message from state machine");
    }

    if (*init_request == std::nullopt) {
      return absl::InternalError("No outgoing message but session not open");
    }

    absl::Status send_result = transport->Send(**init_request);
    if (!send_result.ok()) {
      return util::status::Annotate(send_result,
                                    "Failed to send outgoing message");
    }

    // Some initialization seqeuences may end with the client sending a final
    // request but not expecting any response from the server.
    if ((*session)->IsOpen()) {
      break;
    }

    absl::StatusOr<session::v1::SessionResponse> init_response =
        transport->Receive();
    if (!init_response.ok()) {
      return util::status::Annotate(
          init_request.status(),
          "Failed to get next init response from server");
    }

    absl::Status put_result = (*session)->PutIncomingMessage(*init_response);
    if (!put_result.ok()) {
      return util::status::Annotate(
          put_result,
          "Failed to put next init response in session state machine");
    }
  }

  // Need to call private constructor, so WrapUnique instead of make_unique.
  return absl::WrapUnique(
      new Channel(std::move(*session), std::move(transport)));
}

}  // namespace oak::client
