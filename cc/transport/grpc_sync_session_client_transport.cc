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

#include "cc/transport/grpc_sync_session_client_transport.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "cc/oak_session/client_session.h"
#include "grpcpp/support/sync_stream.h"
#include "proto/session/session.pb.h"

namespace oak::transport {

absl::Status GrpcSyncSessionClientTransport::Send(
    session::v1::SessionRequest&& message) {
  absl::MutexLock lock(&mtx_);
  if (half_closed_) {
    return absl::InternalError("Already half-closed.");
  }
  if (!stream_->Write(message)) {
    return absl::AbortedError("Failed to write outgoing message.");
  }
  return absl::OkStatus();
}

absl::StatusOr<session::v1::SessionResponse>
GrpcSyncSessionClientTransport::Receive() {
  session::v1::SessionResponse response;
  if (!stream_->Read(&response)) {
    return absl::AbortedError("Failed to readin incoming message.");
  }
  return response;
}

void GrpcSyncSessionClientTransport::HalfClose() {
  absl::MutexLock lock(&mtx_);
  if (half_closed_) {
    return;
  }
  stream_->WritesDone();
  half_closed_ = true;
}

};  // namespace oak::transport
