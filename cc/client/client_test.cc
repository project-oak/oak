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

#include "cc/client/client.h"

#include <chrono>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/attestation/verification/attestation_verifier.h"
#include "cc/crypto/encryption_key.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/server_encryptor.h"
#include "cc/transport/transport.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/session/messages.pb.h"

namespace oak::client {
namespace {

using ::oak::attestation::v1::AttestationResults;
using ::oak::attestation::v1::Endorsements;
using ::oak::attestation::v1::Evidence;
using ::oak::attestation::verification::AttestationVerifier;
using ::oak::crypto::EncryptionKeyProvider;
using ::oak::crypto::ServerEncryptor;
using ::oak::crypto::v1::EncryptedRequest;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::EndorsedEvidence;
using ::oak::transport::TransportWrapper;
using ::testing::StrEq;

constexpr absl::string_view kTestRequest = "Request";
constexpr absl::string_view kTestResponse = "Response";
constexpr absl::string_view kTestAssociatedData = "";

class OakClientTest : public testing::Test {
 protected:
  void SetUp() override {
    auto encryption_key = EncryptionKeyProvider::Create();
    if (!encryption_key.ok()) {
      return;
    }
    encryption_key_ = std::make_shared<EncryptionKeyProvider>(*encryption_key);
  }

  std::shared_ptr<EncryptionKeyProvider> encryption_key_;
};

// TODO(#3641): Send test remote attestation report to the client and add
// corresponding tests.
class TestTransport : public TransportWrapper {
 public:
  explicit TestTransport(std::shared_ptr<EncryptionKeyProvider> encryption_key)
      : encryption_key_(encryption_key) {}

  absl::StatusOr<EndorsedEvidence> GetEndorsedEvidence() override {
    return EndorsedEvidence();
  }

  absl::StatusOr<EncryptedResponse> Invoke(
      const EncryptedRequest& encrypted_request) override {
    ServerEncryptor server_encryptor = ServerEncryptor(*encryption_key_);
    auto decrypted_request = server_encryptor.Decrypt(encrypted_request);
    if (!decrypted_request.ok()) {
      return decrypted_request.status();
    }

    if (decrypted_request->plaintext != kTestRequest) {
      return absl::InvalidArgumentError(
          std::string("incorrect request, expected: ") +
          std::string(kTestRequest) +
          ", got : " + decrypted_request->plaintext);
    }

    return server_encryptor.Encrypt(kTestResponse, kTestAssociatedData);
  }

 private:
  std::shared_ptr<EncryptionKeyProvider> encryption_key_;
};

class TestAttestationVerifier : public AttestationVerifier {
 public:
  explicit TestAttestationVerifier(
      std::shared_ptr<EncryptionKeyProvider> encryption_key)
      : encryption_key_(encryption_key) {}

  absl::StatusOr<::oak::attestation::v1::AttestationResults> Verify(
      std::chrono::time_point<std::chrono::system_clock> now,
      const Evidence& evidence,
      const Endorsements& endorsements) const override {
    AttestationResults attestation_results;
    attestation_results.set_status(AttestationResults::STATUS_SUCCESS);
    *attestation_results.mutable_encryption_public_key() =
        encryption_key_->GetSerializedPublicKey();
    return attestation_results;
  }

 private:
  std::shared_ptr<EncryptionKeyProvider> encryption_key_;
};

// Client can process attestation evidence and invoke the backend.
TEST_F(OakClientTest, ClientCreateAndInvokeSuccess) {
  auto transport = std::make_unique<TestTransport>(encryption_key_);
  auto verifier = TestAttestationVerifier(encryption_key_);

  auto oak_client = OakClient::Create(std::move(transport), verifier);
  ASSERT_TRUE(oak_client.ok());

  auto response = (*oak_client)->Invoke(kTestRequest);
  ASSERT_TRUE(response.ok());
  EXPECT_THAT(*response, StrEq(kTestResponse));
}

}  // namespace
}  // namespace oak::client
