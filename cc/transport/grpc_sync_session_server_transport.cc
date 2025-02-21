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

#include "cc/transport/grpc_sync_session_server_transport.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "cc/oak_session/server_session.h"
#include "proto/session/session.pb.h"

namespace oak::transport {

absl::Status GrpcSyncSessionServerTransport::Send(
    session::v1::SessionResponse&& message) {
  absl::MutexLock lock(&mtx_);
  if (half_closed_) {
    return absl::InternalError("Already half-closed.");
  }
  if (!stream_->Write(message)) {
    return absl::AbortedError("Failed to write outgoing message.");
  }
  return absl::OkStatus();
}

absl::StatusOr<session::v1::SessionRequest>
GrpcSyncSessionServerTransport::Receive() {
  session::v1::SessionRequest request;
  if (!stream_->Read(&request)) {
    return absl::AbortedError("Failed to read incoming message.");
  }
  return request;
}

void GrpcSyncSessionServerTransport::HalfClose() {
  absl::MutexLock lock(&mtx_);
  half_closed_ = true;
}

}  // namespace oak::transport
