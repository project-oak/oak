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

#ifndef CC_SERVER_OAK_SERVER_CHANNEL_H_
#define CC_SERVER_OAK_SERVER_CHANNEL_H_

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/oak_session/channel/oak_session_channel.h"
#include "cc/oak_session/server_session.h"
#include "proto/session/session.pb.h"

namespace oak::server {

class OakSessionServer {
 public:
  using Channel =
      session::channel::OakSessionChannel<session::v1::SessionResponse,
                                          session::v1::SessionRequest,
                                          session::ServerSession>;

  OakSessionServer() = default;

  // Create a new OakServerChannel instance with the provided session and
  // transport.
  //
  // server_session should be a newly created ServerSession instance with a
  // configuration that matches the configuration of the target server.
  //
  // The call will block during the initialization sequence, and return an open
  // channel that is ready to use, or return an error if the handshake didn't
  // succeed.
  absl::StatusOr<std::unique_ptr<Channel>> NewChannel(
      std::unique_ptr<OakSessionServer::Channel::Transport> transport);
};

}  // namespace oak::server

#endif  // CC_SERVER_OAK_SERVER_CHANNEL_H_
