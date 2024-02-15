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

#include "cc/attestation/cwt.h"

#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::attestation {
namespace {

using ::oak::attestation::v1::Evidence;
using ::testing::ElementsAreArray;
using ::testing::StrEq;

constexpr absl::string_view kTestEvidencePath =
    "oak_attestation_verification/testdata/evidence.textproto";
// Public key extracted from the `kTestEvidencePath` `encryption_public_key_certificate`.
const std::vector<uint8_t> kTestPublicKey = {65,  95,  220, 63,  244, 115, 90,  84,  22,  86,  100,
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
  }

  std::string public_key_certificate_;
};

TEST_F(CertificateTest, CwtDeserializeSuccess) {
  auto certificate_vector =
      std::vector<uint8_t>(public_key_certificate_.begin(), public_key_certificate_.end());
  auto cwt = Cwt::Deserialize(certificate_vector);
  if (!cwt.ok()) {
    std::cerr << "Error: " << cwt.status() << std::endl;
  }
  ASSERT_TRUE(cwt.ok());
  EXPECT_THAT(cwt->subject_public_key.GetPublicKey(), ElementsAreArray(kTestPublicKey));
}

}  // namespace
}  // namespace oak::attestation
