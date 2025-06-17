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

// From https://beacon.nist.gov/beacon/2.0/chain/2/pulse/1352280
const int64_t kTestNistChainId = 2;
const int64_t kTestNistPulseId = 1352280;
constexpr absl::string_view kTestNistOutputValue = absl::string_view(
    "\xb0\x97\x47\x45\x08\xda\x9e\xef\xea\x3d\xc1\x0f\x88\x2f\x92\x62\xc6\xf2"
    "\xd3\xd9\xf4\x28\xfc\xf9\x81\xbb\x67\x27\x1d\xa5\x76\x06\x22\x6e\x1e\x13"
    "\x8e\xdd\x48\x17\x12\xf6\xdb\xaf\x6b\xca\x1b\x3e\x0e\x55\xfb\x3f\x20\x11"
    "\xec\x4f\xff\xba\xd5\xa5\x63\x5e\x72\x2e");

namespace oak::crypto {
namespace {

using namespace ::testing;

using ::oak::crypto::v1::Certificate;
using ::oak::crypto::v1::CertificatePayload;
using ::oak::crypto::v1::ProofOfFreshness;
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

  EXPECT_THAT(deserialized_payload.has_proof_of_freshness(), IsFalse());
}

TEST(CertificateAuthorityTest, GenerateCertificate_WithProofOfFreshness) {
  Signature mock_signature;
  mock_signature.set_signature(kTestSignature);
  auto mock_signer = std::make_unique<MockSigner>();
  EXPECT_CALL(*mock_signer, Sign(_)).Times(1).WillOnce(Return(mock_signature));

  auto mock_clock = std::make_unique<MockClock>();
  EXPECT_CALL(*mock_clock, CurrentTime())
      .Times(1)
      .WillOnce(Return(absl::UnixEpoch() +
                       absl::Milliseconds(kTestCurrentTimeMillseconds)));

  ProofOfFreshness test_proof_of_freshness;
  test_proof_of_freshness.set_nist_chain_index(kTestNistChainId);
  test_proof_of_freshness.set_nist_pulse_index(kTestNistPulseId);
  test_proof_of_freshness.set_nist_pulse_output_value(kTestNistOutputValue);

  auto certificate_authority =
      CertificateAuthority(std::move(mock_signer), std::move(mock_clock));

  const auto kTestValidity = absl::Hours(1);
  absl::StatusOr<Certificate> certificate =
      certificate_authority.GenerateCertificate(kTestSubjectPublicKey,
                                                kTestPurposeId, kTestValidity,
                                                &test_proof_of_freshness);
  ASSERT_TRUE(certificate.ok());

  CertificatePayload deserialized_payload;
  ASSERT_TRUE(deserialized_payload.ParseFromString(
      (*certificate).serialized_payload()));

  EXPECT_TRUE(deserialized_payload.has_proof_of_freshness());

  EXPECT_EQ(deserialized_payload.proof_of_freshness().nist_chain_index(),
            kTestNistChainId);
  EXPECT_EQ(deserialized_payload.proof_of_freshness().nist_pulse_index(),
            kTestNistPulseId);
  EXPECT_EQ(deserialized_payload.proof_of_freshness().nist_pulse_output_value(),
            kTestNistOutputValue);
}

}  // namespace
}  // namespace oak::crypto
