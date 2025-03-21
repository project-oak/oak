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
#include "cc/oak_session/config.h"
#include "cc/oak_session/server_session.h"
#include "proto/session/session.pb.h"

namespace oak::server {

// A lightweight class that can be used to create new attested, encrypted
// channels using a consistent configuration, for implementing server-side
// handlers.
class OakSessionServer {
 public:
  using Channel =
      session::channel::OakSessionChannel<session::v1::SessionResponse,
                                          session::v1::SessionRequest,
                                          session::ServerSession>;

  // A valid `SessionConfig` can be obtained using
  // oak::session::SessionConfigBuilder. Each session needs its own unique
  // SessionConfig instance, so a function to create a new SessionConfig should
  // be provided.
  OakSessionServer(
      absl::AnyInvocable<session::SessionConfig*()> config_provider)
      : config_provider_(std::move(config_provider)) {}

  // Use a default configuration provider, Unattested + NoiseNN
  ABSL_DEPRECATED("Use the config-providing variant.")
  OakSessionServer()
      : OakSessionServer([] {
          return session::SessionConfigBuilder(
                     session::AttestationType::kUnattested,
                     session::HandshakeType::kNoiseNN)
              .Build();
        }) {}

  // Keeping this around briefly until we transition existing clients.
  ABSL_DEPRECATED(
      "This constructor will lead to UB. Use the config-provider-providing "
      "variant.")
  OakSessionServer(session::SessionConfig* config)
      : OakSessionServer([config] { return config; }) {}

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

 private:
  absl::AnyInvocable<session::SessionConfig*()> config_provider_;
};

}  // namespace oak::server

#endif  // CC_SERVER_OAK_SERVER_CHANNEL_H_
