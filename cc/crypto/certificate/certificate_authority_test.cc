/*
 * Copyright 2025 The Project Oak Authors
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

#include "cc/crypto/certificate/certificate_authority.h"

#include <memory>
#include <utility>

#include "absl/time/time.h"
#include "cc/crypto/signing_key.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

constexpr uint64_t kTestCurrentTimeMillseconds = 60000;
const char* kTestSubjectPublicKey = "TEST SUBJECT PUBLIC KEY";
const char* kTestPurposeId = "TEST PURPOSE ID";
const char* kTestSignature = "TEST SIGNATURE";

namespace oak::crypto {
namespace {

using namespace ::testing;

using ::oak::crypto::v1::Certificate;
using ::oak::crypto::v1::CertificatePayload;
using ::oak::crypto::v1::Signature;

class MockSigner : public SigningKeyHandle {
 public:
  MOCK_METHOD(absl::StatusOr<Signature>, Sign, (absl::string_view message),
              (override));
};

class MockClock : public Clock {
 public:
  MOCK_METHOD(absl::Time, CurrentTime, (), (const, override));
};

TEST(CertificateAuthorityTest, GenerateCertificateSuccess) {
  Signature mock_signature;
  mock_signature.set_signature(kTestSignature);
  auto mock_signer = std::make_unique<MockSigner>();
  EXPECT_CALL(*mock_signer, Sign(_)).Times(1).WillOnce(Return(mock_signature));

  auto mock_clock = std::make_unique<MockClock>();
  EXPECT_CALL(*mock_clock, CurrentTime())
      .Times(1)
      .WillOnce(Return(absl::UnixEpoch() +
                       absl::Milliseconds(kTestCurrentTimeMillseconds)));

  auto certificate_authority =
      CertificateAuthority(std::move(mock_signer), std::move(mock_clock));

  const auto kTestValidity = absl::Hours(1);
  absl::StatusOr<Certificate> result =
      certificate_authority.GenerateCertificate(kTestSubjectPublicKey,
                                                kTestPurposeId, kTestValidity);
  ASSERT_TRUE(result.ok());
  const Certificate& certificate = result.value();
  EXPECT_EQ(certificate.signature_info().signature(), kTestSignature);

  CertificatePayload deserialized_payload;
  ASSERT_TRUE(
      deserialized_payload.ParseFromString(certificate.serialized_payload()));
  EXPECT_EQ(deserialized_payload.subject_public_key_info().public_key(),
            kTestSubjectPublicKey);
  EXPECT_EQ(deserialized_payload.subject_public_key_info().purpose_id(),
            kTestPurposeId);

  auto not_before = FromTimestamp(deserialized_payload.validity().not_before());
  auto expected_not_before =
      absl::UnixEpoch() + absl::Milliseconds(kTestCurrentTimeMillseconds);
  EXPECT_EQ(not_before, expected_not_before);

  auto not_after = FromTimestamp(deserialized_payload.validity().not_after());
  auto expected_not_after = expected_not_before + kTestValidity;
  EXPECT_EQ(not_after, expected_not_after);

  EXPECT_THAT(not_before, Le(not_after));
}

}  // namespace
}  // namespace oak::crypto
