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
#include "cc/attestation/verification/insecure_attestation_verifier.h"
#include "cc/client/client.h"
#include "cc/containers/hello_world_enclave_app/app_service.h"
#include "cc/containers/sdk/standalone/oak_standalone.h"
#include "cc/transport/grpc_streaming_transport.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "gtest/gtest.h"
#include "oak_containers/examples/hello_world/proto/hello_world.grpc.pb.h"

namespace oak::containers::sdk::standalone {

namespace {

using ::absl_testing::IsOk;
using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::verification::InsecureAttestationVerifier;
using ::oak::client::OakClient;
using ::oak::containers::example::EnclaveApplication;
using ::oak::containers::hello_world_enclave_app::EnclaveApplicationImpl;
using ::oak::crypto::EncryptionKeyProvider;
using ::oak::crypto::KeyPair;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::transport::GrpcStreamingTransport;
using ::testing::Eq;

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
        "{}");

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
  ASSERT_TRUE(client.ok());

  auto result = (*client)->Invoke("Standalone Test");
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(*result,
            "Hello from the enclave, Standalone Test! Btw, the app has a "
            "config with a length of 2 bytes.");
}
}  // namespace

}  // namespace oak::containers::sdk::standalone
