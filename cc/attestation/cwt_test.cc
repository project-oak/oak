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
#include "cc/attestation/certificate.h"

#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <sstream>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "gtest/gtest.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::attestation {
namespace {

using ::oak::attestation::v1::Evidence;
using ::testing::StrEq;

constexpr absl::string_view kTestEvidencePath = "oak_attestation_verification/testdata/evidence.textproto";
// constexpr absl::string_view kTestCertificate = "\204D\241\0018.\241\004RAsymmetricECDSA256Y\001\n\245\001x(287480ca6870702463f65a82eb04ca0e4a69f63a\002x(0efe5c6124c03421454daaa8e7cdbd82033fef83:\000GDWXD\246\001\001\002T\016\376\\a$\3004!EM\252\250\347\315\275\202\003?\357\203\0038\036\004\201\005 \004!X A_\334?\364sZT\026Vd\031\0341\027\034\n\203,\263\272\253\237\320\221\271Bl\215\210\230;:\000GDXB \000:\000GD^\242:\000GDh\241:\000GDkX \330\310>5\215\374\231\256\246\302\000\032\327m\273ji\253\213\311\335\321*7\tZ\035\250V\226\223X:\000GDi\241:\000GDkX \033\336\262\213\304\362\020\333\233B\2421`\370\027\307\005\357\371\210\334g\302\342\350\356O\216\345\223RzX@\346J\005w\t1o\014\n]$\036/}\226P\226^y\201N\216\307q\240*\n\325`\316\256\320\214z\331ge\031\335\217+\016l\257$W\004\375\250\216\305-\357\216\311\234Mo\210\3464\016\340\202";
// const char* kTestCertificate = "\204D\241\0018.\241\004RAsymmetricECDSA256Y\001\n\245\001x(287480ca6870702463f65a82eb04ca0e4a69f63a\002x(0efe5c6124c03421454daaa8e7cdbd82033fef83:\000GDWXD\246\001\001\002T\016\376\\a$\3004!EM\252\250\347\315\275\202\003?\357\203\0038\036\004\201\005 \004!X A_\334?\364sZT\026Vd\031\0341\027\034\n\203,\263\272\253\237\320\221\271Bl\215\210\230;:\000GDXB \000:\000GD^\242:\000GDh\241:\000GDkX \330\310>5\215\374\231\256\246\302\000\032\327m\273ji\253\213\311\335\321*7\tZ\035\250V\226\223X:\000GDi\241:\000GDkX \033\336\262\213\304\362\020\333\233B\2421`\370\027\307\005\357\371\210\334g\302\342\350\356O\216\345\223RzX@\346J\005w\t1o\014\n]$\036/}\226P\226^y\201N\216\307q\240*\n\325`\316\256\320\214z\331ge\031\335\217+\016l\257$W\004\375\250\216\305-\357\216\311\234Mo\210\3464\016\340\202";
// constexpr absl::string_view kTestPublicKey = "";

class CertificateTest : public testing::Test {
 protected:
  void SetUp() override {
    std::ifstream test_evidence_file(kTestEvidencePath.data());
    ASSERT_TRUE(test_evidence_file);
    google::protobuf::io::IstreamInputStream test_evidence_protobuf_stream(&test_evidence_file);

    auto test_evidence = std::make_unique<Evidence>();
    bool parse_success = google::protobuf::TextFormat::Parse(&test_evidence_protobuf_stream, test_evidence.get());
    ASSERT_TRUE(parse_success);

    test_evidence_ = std::move(test_evidence);
  }

  std::unique_ptr<Evidence> test_evidence_;
};

TEST_F(CertificateTest, ExtractPublicKeyFromCwtCertificateSuccess) {

  // auto [item, end, error] = cppbor::parse(reinterpret_cast<const uint8_t*>(kTestCertificate.c_str()), kTestCertificate.length());
  // if (!error.empty()) {
  //   std::cerr << "couldn't parse CBOR: " << error << std::endl;
  // }

  // std::cerr << "Certificate string: " << kTestCertificate << std::endl;
  // std::cerr << "kTestCertificate.size(): " << sizeof(kTestCertificate) << std::endl;

  auto certificate_proto = test_evidence_->application_keys().encryption_public_key_certificate();
  auto certificate_vector = std::vector<uint8_t>(certificate_proto.begin(), certificate_proto.end());
  // auto certificate = std::vector<uint8_t>(kTestCertificate, sizeof(kTestCertificate));
  auto result = ExtractPublicKeyFromCwtCertificate(certificate_vector);
  if (!result.ok()) {
    std::cerr << "Error: " << result.status() << std::endl;
  }
  ASSERT_TRUE(result.ok());
  // EXPECT_THAT(*result, StrEq(kTestPublicKey));
}

}  // namespace
}  // namespace oak::attestation
