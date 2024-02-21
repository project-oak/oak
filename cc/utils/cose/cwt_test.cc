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
#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::utils::cose {
namespace {

using ::oak::attestation::v1::Evidence;
using ::testing::ElementsAreArray;

constexpr absl::string_view kTestEvidencePath =
    "oak_attestation_verification/testdata/evidence.textproto";
// Public key extracted from the `kTestEvidencePath` `encryption_public_key_certificate`.
constexpr uint8_t kTestPublicKey[] = {65,  95,  220, 63,  244, 115, 90,  84,  22,  86,  100,
                                      25,  28,  49,  23,  28,  10,  131, 44,  179, 186, 171,
                                      159, 208, 145, 185, 66,  108, 141, 136, 152, 59};

class CertificateTest : public testing::Test {
 protected:
  void SetUp() override {
    std::ifstream test_evidence_file(kTestEvidencePath.data());
    ASSERT_TRUE(test_evidence_file);
    google::protobuf::io::IstreamInputStream test_evidence_protobuf_stream(&test_evidence_file);

    auto test_evidence = std::make_unique<Evidence>();
    bool parse_success =
        google::protobuf::TextFormat::Parse(&test_evidence_protobuf_stream, test_evidence.get());
    ASSERT_TRUE(parse_success);

    public_key_certificate_ = test_evidence->application_keys().encryption_public_key_certificate();
    test_public_key_ = std::vector<uint8_t>
  }

  std::string public_key_certificate_;
};

TEST_F(CertificateTest, CwtDeserializeSuccess) {
  auto cwt = Cwt::Deserialize(public_key_certificate_);
  EXPECT_TRUE(cwt.ok()) << cwt.status();
  EXPECT_THAT(cwt->subject_public_key.GetPublicKey(), ElementsAreArray(kTestPublicKey));
}

TEST_F(CertificateTest, CwtSerializeDeserializeSuccess) {
  std::vector<uint8_t> test_public_key = {1, 2, 3, 4};
  auto serialized_cwt = Cwt::SerializeHpkePublicKey(test_public_key);
  EXPECT_TRUE(serialized_cwt.ok()) << serialized_cwt.status();

  auto deserialized_cwt = Cwt::Deserialize(*serialized_cwt);
  EXPECT_TRUE(deserialized_cwt.ok()) << deserialized_cwt.status();
  EXPECT_THAT(deserialized_cwt->subject_public_key.GetPublicKey(), ElementsAreArray(test_public_key));
}

}  // namespace
}  // namespace oak::utils::cose
