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

#include <grpc/grpc.h>
#include <grpcpp/channel.h>
#include <grpcpp/client_context.h>
#include <grpcpp/create_channel.h>
#include <grpcpp/grpcpp.h>
#include <grpcpp/security/credentials.h>

#include <memory>

#include "cc/client/client.h"
#include "cc/remote_attestation/insecure_attestation_verifier.h"
#include "cc/transport/grpc_streaming_transport.h"
#include "oak_remote_attestation/proto/v1/service_streaming.grpc.pb.h"

using ::grpc::Channel;
using ::grpc::ClientContext;
using ::grpc::ClientReaderWriter;
using ::grpc::CreateChannel;
using ::grpc::InsecureChannelCredentials;
using ::oak::client::OakClient;
using ::oak::remote_attestation::InsecureAttestationVerifier;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;
using ::oak::session::v1::StreamingSession;
using ::oak::transport::GrpcStreamingTransport;

// TODO(#4069): Finish CLI implementation.
int main(int argc, char* argv[]) {
  // Create gRPC client stub.
  std::shared_ptr<Channel> channel = CreateChannel("", InsecureChannelCredentials());
  std::shared_ptr<oak::session::v1::StreamingSession::Stub> stub =
      StreamingSession::NewStub(channel);
  ClientContext context;
  // auto channel_reader_writer = stub->Stream(&context);
  std::unique_ptr<ClientReaderWriter<RequestWrapper, ResponseWrapper>> channel_reader_writer =
      stub->Stream(&context);

  // Create Oak Client.
  std::unique_ptr<GrpcStreamingTransport> transport = std::make_unique<GrpcStreamingTransport>(
      GrpcStreamingTransport(std::move(channel_reader_writer)));
  InsecureAttestationVerifier verifier = InsecureAttestationVerifier();
  absl::StatusOr<std::unique_ptr<OakClient>> oak_client =
      OakClient::Create(std::move(transport), verifier);
  if (!oak_client.ok()) {
    // TODO(#4069): Log errors.
    return 1;
  }
}
