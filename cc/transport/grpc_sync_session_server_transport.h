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

#ifndef CC_TRANSPORT_GRPC_SYNC_SESSION_SERVER_TRANSPORT_H_
#define CC_TRANSPORT_GRPC_SYNC_SESSION_SERVER_TRANSPORT_H_

#include "absl/base/thread_annotations.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "cc/oak_session/channel/oak_session_channel.h"
#include "cc/oak_session/server_session.h"
#include "cc/server/session_server.h"
#include "grpcpp/support/sync_stream.h"
#include "proto/session/session.pb.h"

namespace oak::transport {

// An implementation of `OakSessionChannel::Transport` for use with
// `OakSessionServer`, using the synchronous gRPC streaming interface.
class GrpcSyncSessionServerTransport
    : public ::oak::server::OakSessionServer::Channel::Transport {
 public:
  explicit GrpcSyncSessionServerTransport(
      grpc::ServerReaderWriterInterface<session::v1::SessionResponse,
                                        session::v1::SessionRequest>* stream)
      : stream_(stream) {}

  absl::Status Send(session::v1::SessionResponse&& message) override;
  absl::StatusOr<session::v1::SessionRequest> Receive() override;
  void HalfClose() override;

 private:
  grpc::ServerReaderWriterInterface<session::v1::SessionResponse,
                                    session::v1::SessionRequest>* stream_;
  absl::Mutex mtx_;
  bool half_closed_ ABSL_GUARDED_BY(mtx_) = false;
};

}  // namespace oak::transport

#endif  //  CC_TRANSPORT_GRPC_SYNC_SESSION_SERVER_TRANSPORT_H_
