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

#include "cc/utils/cose/cwt.h"

#include <cstdint>
#include <fstream>
#include <memory>
#include <string>
#include <vector>

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::utils::cose {
namespace {

using ::oak::attestation::v1::Evidence;
using ::testing::ElementsAreArray;

constexpr absl::string_view kTestEvidencePath =
    "oak_attestation_verification/testdata/milan_oc_staging_evidence.binarypb";

// Public key extracted from the `kTestEvidencePath`
// `encryption_public_key_certificate`.
constexpr uint8_t kTestPublicKey[] = {146, 168, 171, 112, 97,  113, 10,  95,
                                      36,  223, 0,   29,  154, 253, 246, 188,
                                      154, 43,  252, 192, 229, 178, 185, 231,
                                      234, 233, 158, 86,  139, 40,  252, 106};

class CertificateTest : public testing::Test {
 protected:
  void SetUp() override {
    std::ifstream stream(kTestEvidencePath.data());
    ASSERT_TRUE(stream);
    auto evidence = std::make_unique<Evidence>();
    ASSERT_TRUE(evidence->ParseFromIstream(&stream));
    public_key_certificate_ =
        evidence->application_keys().encryption_public_key_certificate();
  }

  std::string public_key_certificate_;
};

TEST_F(CertificateTest, CwtDeserializeSuccess) {
  auto cwt = Cwt::Deserialize(public_key_certificate_);
  EXPECT_TRUE(cwt.ok()) << cwt.status();
  EXPECT_THAT(cwt->subject_public_key.GetPublicKey(),
              ElementsAreArray(kTestPublicKey));
}

TEST_F(CertificateTest, CwtSerializeDeserializeSuccess) {
  std::vector<uint8_t> test_public_key = {1, 2, 3, 4};
  auto serialized_cwt = Cwt::SerializeHpkePublicKey(test_public_key);
  EXPECT_TRUE(serialized_cwt.ok()) << serialized_cwt.status();
  auto serialized_cwt_string =
      std::string(serialized_cwt->begin(), serialized_cwt->end());

  auto deserialized_cwt = Cwt::Deserialize(serialized_cwt_string);
  EXPECT_TRUE(deserialized_cwt.ok()) << deserialized_cwt.status();
  EXPECT_THAT(deserialized_cwt->subject_public_key.GetPublicKey(),
              ElementsAreArray(test_public_key));
}

}  // namespace
}  // namespace oak::utils::cose
