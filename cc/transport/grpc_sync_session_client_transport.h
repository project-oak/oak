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

#ifndef CC_TRANSPORT_GRPC_SYNC_CLIENT_SESSION_TRANSPORT_H_
#define CC_TRANSPORT_GRPC_SYNC_CLIENT_SESSION_TRANSPORT_H_

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/client/session_client.h"
#include "cc/oak_session/channel/oak_session_channel.h"
#include "cc/oak_session/client_session.h"
#include "grpcpp/support/sync_stream.h"
#include "proto/session/session.pb.h"

namespace oak::transport {

// An implementation of `OakSessionChannel::Transport` for use with
// `OakSessionClient` using the gRPC synchronous streaming interface.
class GrpcSyncSessionClientTransport
    : public ::oak::client::OakSessionClient::Channel::Transport {
 public:
  explicit GrpcSyncSessionClientTransport(
      std::unique_ptr<grpc::ClientReaderWriterInterface<
          session::v1::SessionRequest, session::v1::SessionResponse>>
          stream)
      : stream_(std::move(stream)) {}

  absl::Status Send(session::v1::SessionRequest&& message) override;
  absl::StatusOr<session::v1::SessionResponse> Receive() override;

 private:
  std::unique_ptr<grpc::ClientReaderWriterInterface<
      session::v1::SessionRequest, session::v1::SessionResponse>>
      stream_;
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_GRPC_SYNC_CLIENT_SESSION_TRANSPORT_H_
