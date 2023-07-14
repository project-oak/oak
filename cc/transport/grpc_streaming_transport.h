/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_
#define CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_

#include <memory>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/transport/transport.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"
#include "oak_remote_attestation/proto/v1/service_streaming.grpc.pb.h"
#include "oak_remote_attestation/proto/v1/service_streaming.pb.h"

namespace oak::transport {

class GrpcStreamingTransport : public TransportWrapper {
 public:
  explicit GrpcStreamingTransport(
      std::unique_ptr<::grpc::ClientReaderWriter<::oak::session::v1::RequestWrapper,
                                                 ::oak::session::v1::ResponseWrapper>>
          channel_reader_writer)
      : channel_reader_writer_(std::move(channel_reader_writer)) {}

  absl::StatusOr<::oak::session::v1::AttestationBundle> GetEvidence() override;
  absl::StatusOr<std::string> Invoke(absl::string_view request_bytes) override;

  ~GrpcStreamingTransport() override;

 private:
  std::unique_ptr<::grpc::ClientReaderWriter<::oak::session::v1::RequestWrapper,
                                             ::oak::session::v1::ResponseWrapper>>
      channel_reader_writer_;

  absl::StatusOr<::oak::session::v1::ResponseWrapper> Send(
      const ::oak::session::v1::RequestWrapper& request);
  absl::Status Close();
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_GRPC_STREAMING_TRANSPORT_H_
