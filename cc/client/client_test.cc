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

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "cc/crypto/server_encryptor.h"
#include "cc/remote_attestation/insecure_attestation_verifier.h"
#include "cc/transport/transport.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "oak_remote_attestation/proto/v1/messages.pb.h"

namespace oak::client {
namespace {

using ::oak::crypto::KeyPair;
using ::oak::crypto::ServerEncryptor;
using ::oak::remote_attestation::InsecureAttestationVerifier;
using ::oak::session::v1::AttestationBundle;
using ::oak::transport::TransportWrapper;
using ::testing::StrEq;

constexpr absl::string_view kTestRequest = "Request";
constexpr absl::string_view kTestResponse = "Response";
constexpr absl::string_view kTestAssociatedData = "";

// Number of message exchanges done to test secure session handling.
constexpr uint8_t kTestSessionSize = 8;

// TODO(#3641): Send test remote attestation report to the client and add corresponding tests.
class TestTransport : public TransportWrapper {
 public:
  TestTransport() : key_pair_(*KeyPair::Generate()) {}

  absl::StatusOr<AttestationBundle> GetEvidence() override {
    AttestationBundle endorsed_evidence;
    endorsed_evidence.mutable_attestation_evidence()->set_encryption_public_key(
        key_pair_.public_key);
    return endorsed_evidence;
  }

  absl::StatusOr<std::string> Invoke(absl::string_view request_bytes) override {
    ServerEncryptor server_encryptor = ServerEncryptor(key_pair_);
    auto decrypted_request = server_encryptor.Decrypt(request_bytes);
    if (!decrypted_request.ok()) {
      return decrypted_request.status();
    }

    if (decrypted_request->plaintext != kTestRequest) {
      return absl::InvalidArgumentError(std::string("incorrect request, expected: ") +
                                        std::string(kTestRequest) +
                                        ", got : " + decrypted_request->plaintext);
    }

    return server_encryptor.Encrypt(kTestResponse, kTestAssociatedData);
  }

 private:
  KeyPair key_pair_;
};

// Client can process attestation evidence and invoke the backend.
TEST(EncryptorTest, ClientCreateAndInvokeSuccess) {
  auto transport = std::make_unique<TestTransport>();
  InsecureAttestationVerifier verifier = InsecureAttestationVerifier();
  auto oak_client = OakClient::Create(std::move(transport), verifier);
  ASSERT_TRUE(oak_client.ok());

  for (int i = 0; i < kTestSessionSize; i++) {
    auto response = (*oak_client)->Invoke(kTestRequest);
    ASSERT_TRUE(response.ok());
    EXPECT_THAT(*response, StrEq(kTestResponse));
  }
}

}  // namespace
}  // namespace oak::client
