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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/client/client.h"
#include "cc/remote_attestation/InsecureAttestationVerifier.h"
#include "cc/transport/grpc_streaming_transport.h"
#include "oak_remote_attestation/proto/v1/service_streaming.grpc.pb.h"

int main(int argc, char* argv[]) {
  // // InitGoogle(argv[0], &argc, &argv, /*remove_flags=*/true);
  // absl::ParseCommandLine(argc, argv);

  // std::string address = absl::GetFlag(FLAGS_address);
  // // std::string request = absl::GetFlag(FLAGS_request);
  // LOG(INFO) << "Connecting to: " << address;

  // // Create gRPC client stub.
  // std::shared_ptr<grpc::Channel> channel =
  //     grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
  // // auto stub = StreamingSession::NewStub(channel);

  // // Create Oak Client.
  // std::unique_ptr<GrpcStreamingTransport> transport = GrpcStreamingTransport::Create(channel);
  // std::unique_ptr<OakClient<GrpcStreamingTransport>> oak_client =
  //     OakClient::Create(transport, InsecureAttestationVerifier());

  // // Send request to the Oak backend.
  // LOG(INFO) << "Sending request: " << absl::GetFlag(FLAGS_request);

  // std::string response = absl::BytesToHexString(response_body);
  // LOG(INFO) << "Received response: " << response;
}
