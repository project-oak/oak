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

#include "cc/utils/variant/variant.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "proto/attestation/endorsement.pb.h"

namespace oak {
namespace {

using ::oak::attestation::v1::AmdSevSnpEndorsement;
using ::oak::attestation::v1::ApplicationEndorsement;
using ::oak::attestation::v1::ContainerEndorsement;
using ::oak::attestation::v1::FirmwareEndorsement;
using ::oak::attestation::v1::KernelEndorsement;
using ::oak::attestation::v1::SystemEndorsement;

template <typename T>
class VariantTest : public testing::Test {
 public:
  bool CompareProtos(const T& proto1, const T& proto2) {
    std::string serialized1, serialized2;
    EXPECT_TRUE(proto1.SerializeToString(&serialized1));
    EXPECT_TRUE(proto2.SerializeToString(&serialized2));
    return serialized1 == serialized2;
  }

  T CreateInstance() { return T(); }
};

TYPED_TEST_SUITE_P(VariantTest);

TYPED_TEST_P(VariantTest, Inverse) {
  TypeParam expected = this->CreateInstance();
  TypeParam actual = FromVariant<TypeParam>(ToVariant(expected)).value();
  EXPECT_TRUE(this->CompareProtos(actual, expected));
}

REGISTER_TYPED_TEST_SUITE_P(VariantTest, Inverse);

using TestTypes = testing::Types<AmdSevSnpEndorsement, FirmwareEndorsement,
                                 KernelEndorsement, SystemEndorsement,
                                 ContainerEndorsement, ApplicationEndorsement>;

INSTANTIATE_TYPED_TEST_SUITE_P(TypedTestSuite, VariantTest, TestTypes);

}  // namespace
}  // namespace oak
