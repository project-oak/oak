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

#include <cstdint>

#include "absl/log/log.h"
#include "absl/status/status_matchers.h"
#include "absl/strings/substitute.h"
#include "cc/attestation/verification/insecure_attestation_verifier.h"
#include "cc/client/client.h"
#include "cc/containers/hello_world_enclave_app/app_service.h"
#include "cc/containers/sdk/standalone/oak_standalone.h"
#include "cc/ffi/rust_bytes.h"
#include "cc/oak_session/client_session.h"
#include "cc/transport/grpc_streaming_transport.h"
#include "gmock/gmock.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gtest/gtest.h"
#include "oak_containers/examples/hello_world/proto/hello_world.grpc.pb.h"

namespace oak::containers::sdk::standalone {

namespace {

using ::absl_testing::IsOk;
using ::absl_testing::IsOkAndHolds;
using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::verification::InsecureAttestationVerifier;
using ::oak::client::OakClient;
using ::oak::containers::example::EnclaveApplication;
using ::oak::containers::hello_world_enclave_app::EnclaveApplicationImpl;
using ::oak::crypto::EncryptionKeyProvider;
using ::oak::crypto::KeyPair;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::oak::transport::GrpcStreamingTransport;
using ::testing::Eq;

constexpr absl::string_view kApplicationConfig = "{}";

class HelloWorldStandaloneTest : public testing::Test {
  void SetUp() override {
    // Set up our new Keypair and get an EndorsedEvidence from Rust.
    absl::StatusOr<KeyPair> key_pair = KeyPair::Generate();
    ASSERT_TRUE(key_pair.ok()) << key_pair.status();
    absl::StatusOr<EndorsedEvidence> endorsed_evidence =
        GetEndorsedEvidence(*key_pair);
    ASSERT_THAT(endorsed_evidence, IsOk());

    // Verify that the endorsed evidence is valid.
    InsecureAttestationVerifier verifier;
    absl::StatusOr<AttestationResults> attestation_results = verifier.Verify(
        std::chrono::system_clock::now(), endorsed_evidence->evidence(),
        endorsed_evidence->endorsements());
    ASSERT_THAT(attestation_results, IsOk());

    service_ = std::make_unique<EnclaveApplicationImpl>(
        OakSessionContext(std::move(*endorsed_evidence),
                          std::make_unique<EncryptionKeyProvider>(*key_pair)),
        kApplicationConfig);

    grpc::ServerBuilder builder;
    builder.AddListeningPort("[::]:8080", grpc::InsecureServerCredentials());
    builder.RegisterService(service_.get());
    server_ = builder.BuildAndStart();

    auto channel = server_->InProcessChannel({});
    stub_ = EnclaveApplication::NewStub(channel);
  }

 protected:
  std::unique_ptr<EnclaveApplicationImpl> service_;
  std::unique_ptr<grpc::Server> server_;
  std::unique_ptr<EnclaveApplication::Stub> stub_;
};

TEST_F(HelloWorldStandaloneTest, LegacySessionReturnsResponse) {
  grpc::ClientContext context;
  auto transport =
      std::make_unique<GrpcStreamingTransport>(stub_->LegacySession(&context));
  InsecureAttestationVerifier verifier;
  auto client = OakClient::Create(std::move(transport), verifier);
  ASSERT_THAT(client, IsOk());

  auto result = (*client)->Invoke("Standalone Test");
  ASSERT_THAT(result,
              IsOkAndHolds(Eq(absl::Substitute(
                  "Hello from the enclave, Standalone Test! Btw, the app has a "
                  "config with a length of $0 bytes.",
                  kApplicationConfig.size()))));
}

TEST_F(HelloWorldStandaloneTest, OakSessionReturnsResponse) {
  absl::StatusOr<std::unique_ptr<session::ClientSession>> session =
      session::ClientSession::Create(
          session::SessionConfigBuilder(session::AttestationType::kUnattested,
                                        session::HandshakeType::kNoiseNN)
              .Build());

  grpc::ClientContext context;
  std::unique_ptr<grpc::ClientReaderWriterInterface<
      session::v1::SessionRequest, session::v1::SessionResponse>>
      stream = stub_->OakSession(&context);

  // Handshake
  while (!(*session)->IsOpen()) {
    absl::StatusOr<std::optional<session::v1::SessionRequest>>
        outgoing_message = (*session)->GetOutgoingMessage();
    ASSERT_THAT(outgoing_message, IsOk());
    ASSERT_TRUE(stream->Write(**outgoing_message));

    session::v1::SessionResponse response;
    ASSERT_TRUE(stream->Read(&response));
    ASSERT_THAT((*session)->PutIncomingMessage(response), IsOk());
  }

  ASSERT_THAT((*session)->Write("Standalone Test"), IsOk());
  absl::StatusOr<std::optional<session::v1::SessionRequest>> outgoing_message =
      (*session)->GetOutgoingMessage();
  ASSERT_THAT(outgoing_message, IsOk());
  ASSERT_TRUE(stream->Write(**outgoing_message));

  session::v1::SessionResponse response;
  ASSERT_TRUE(stream->Read(&response));
  ASSERT_THAT((*session)->PutIncomingMessage(response), IsOk());
  absl::StatusOr<std::optional<ffi::RustBytes>> unencrypted_response =
      (*session)->ReadToRustBytes();

  ASSERT_THAT(unencrypted_response,
              IsOkAndHolds(std::optional(absl::Substitute(
                  "Hello from the enclave, Standalone Test! Btw, the "
                  "app has a config with a length of $0 bytes.",
                  kApplicationConfig.size()))));
}

}  // namespace

}  // namespace oak::containers::sdk::standalone
