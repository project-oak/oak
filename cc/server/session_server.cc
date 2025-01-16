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

#include "cc/server/session_server.h"

#include <memory>
#include <optional>
#include <utility>

#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/channel/oak_session_channel.h"
#include "cc/oak_session/config.h"
#include "cc/oak_session/server_session.h"
#include "cc/utils/status/status.h"
#include "proto/session/session.pb.h"

namespace oak::server {

absl::StatusOr<std::unique_ptr<OakSessionServer::Channel>>
OakSessionServer::NewChannel(std::unique_ptr<Channel::Transport> transport) {
  auto session = session::ServerSession::Create(config_provider_());
  if (!session.ok()) {
    return util::status::Annotate(session.status(),
                                  "Failed to create server session");
  }

  while (!(*session)->IsOpen()) {
    absl::StatusOr<session::v1::SessionRequest> init_request =
        transport->Receive();
    if (!init_request.ok()) {
      return util::status::Annotate(init_request.status(),
                                    "Failed to get next init message");
    }

    absl::Status put_result = (*session)->PutIncomingMessage(*init_request);
    if (!put_result.ok()) {
      return util::status::Annotate(
          put_result,
          "Failed to put next init message in session state machine");
    }

    absl::StatusOr<std::optional<session::v1::SessionResponse>> init_response =
        (*session)->GetOutgoingMessage();
    if (!init_response.ok()) {
      return util::status::Annotate(
          init_response.status(),
          "Failed to get outgoing message from state machine");
    }

    if (*init_response != std::nullopt) {
      absl::Status send_result = transport->Send(std::move(**init_response));
      if (!send_result.ok()) {
        return util::status::Annotate(send_result,
                                      "Failed to send outgoing message");
      }
    }
  }

  // Need to call private constructor, so WrapUnique instead of make_unique.
  return absl::WrapUnique(
      new Channel(std::move(*session), std::move(transport)));
}

}  // namespace oak::server
