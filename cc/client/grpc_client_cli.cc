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

#include <memory>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/log.h"
#include "cc/attestation/verification/insecure_attestation_verifier.h"
#include "cc/client/client.h"
#include "cc/transport/grpc_streaming_transport.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/grpcpp.h"
#include "grpcpp/security/credentials.h"
#include "proto/session/service_streaming.grpc.pb.h"

using ::grpc::Channel;
using ::grpc::ClientContext;
using ::grpc::ClientReaderWriter;
using ::grpc::CreateChannel;
using ::grpc::InsecureChannelCredentials;
using ::oak::attestation::verification::InsecureAttestationVerifier;
using ::oak::client::OakClient;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;
using ::oak::session::v1::StreamingSession;
using ::oak::transport::GrpcStreamingTransport;

ABSL_FLAG(std::string, address, "", "Address of the backend to connect to");
ABSL_FLAG(std::string, request, "", "Request string to be sent to the backend");

// TODO(#4069): Finish CLI implementation.
int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);
  std::string address = absl::GetFlag(FLAGS_address);
  std::string request = absl::GetFlag(FLAGS_request);

  // Create gRPC client stub.
  LOG(INFO) << "connecting to: " << address;
  std::shared_ptr<Channel> channel =
      CreateChannel(address, InsecureChannelCredentials());
  std::shared_ptr<oak::session::v1::StreamingSession::Stub> stub =
      StreamingSession::NewStub(channel);
  ClientContext context;
  std::unique_ptr<ClientReaderWriter<RequestWrapper, ResponseWrapper>>
      channel_reader_writer = stub->Stream(&context);

  // Create Oak Client.
  LOG(INFO) << "creating Oak Client";
  std::unique_ptr<GrpcStreamingTransport> transport =
      std::make_unique<GrpcStreamingTransport>(
          std::move(channel_reader_writer));
  InsecureAttestationVerifier verifier = InsecureAttestationVerifier();
  absl::StatusOr<std::unique_ptr<OakClient>> oak_client =
      OakClient::Create(std::move(transport), verifier);
  if (!oak_client.ok()) {
    LOG(ERROR) << "couldn't create Oak client: " << oak_client.status();
    return 1;
  }

  LOG(INFO) << "sending request: " << request;
  absl::StatusOr<std::string> response = (*oak_client)->Invoke(request);
  if (!response.ok()) {
    LOG(ERROR) << "couldn't send request: " << response.status();
    return 1;
  }
  LOG(INFO) << "received response: " << *response;
}
