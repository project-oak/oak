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

#include "cc/crypto/tink/signature/verification_utils.h"

#include "absl/status/status.h"
#include "absl/status/status_matchers.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "tink/config/global_registry.h"
#include "tink/configuration.h"
#include "tink/keyset_handle.h"
#include "tink/proto_keyset_format.h"
#include "tink/public_key_sign.h"
#include "tink/public_key_verify.h"
#include "tink/signature/signature_config.h"
#include "tink/signature/signature_key_templates.h"

namespace oak::crypto::tink {
namespace {

using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::Configuration;
using ::crypto::tink::KeyGenConfigGlobalRegistry;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::PublicKeySign;
using ::crypto::tink::PublicKeyVerify;
using ::crypto::tink::SerializeKeysetToProtoKeysetFormat;
using ::crypto::tink::SerializeKeysetWithoutSecretToProtoKeysetFormat;
using ::crypto::tink::SignatureConfig;
using ::crypto::tink::SignatureKeyTemplates;

using ::absl_testing::IsOk;
using ::absl_testing::StatusIs;

const constexpr char* kUnsignedMessage = "Hello World!";

class VerificationUtilsTest : public testing::Test {
 protected:
  void SetUp() override {
    // Create the keyset handle.
    absl::Status signature_registry = SignatureConfig::Register();
    ASSERT_TRUE(signature_registry.ok());
    absl::StatusOr<std::unique_ptr<KeysetHandle>> keyset_handle =
        KeysetHandle::GenerateNew(SignatureKeyTemplates::EcdsaP256(),
                                  KeyGenConfigGlobalRegistry());
    ASSERT_TRUE(keyset_handle.ok());
    keyset_handle_ = std::move(*keyset_handle);

    // Sign the message.
    absl::StatusOr<std::unique_ptr<PublicKeySign>> public_key_sign =
        keyset_handle_->GetPrimitive<PublicKeySign>(ConfigGlobalRegistry());
    ASSERT_TRUE(public_key_sign.ok());

    absl::StatusOr<std::string> signature =
        (*public_key_sign)->Sign(kUnsignedMessage);
    ASSERT_TRUE(signature.ok());
    signature_ = *signature;

    // Get public keyset handle. This should be used for verification.
    // https://developers.google.com/tink/faq/registration_errors#case_2_the_error_lists_a_key_type_and_a_primitive
    absl::StatusOr<std::unique_ptr<KeysetHandle>> public_keyset_handle =
        keyset_handle_->GetPublicKeysetHandle(KeyGenConfigGlobalRegistry());
    ASSERT_TRUE(public_keyset_handle.ok());
    public_keyset_handle_ = std::move(*public_keyset_handle);
  }

  std::unique_ptr<KeysetHandle> keyset_handle_;
  std::unique_ptr<KeysetHandle> public_keyset_handle_;
  std::string signature_;
};

TEST_F(VerificationUtilsTest, VerifySignatureWithTink_Success) {
  absl::StatusOr<std::string> serialized_public_keyset_handle =
      SerializeKeysetWithoutSecretToProtoKeysetFormat(*public_keyset_handle_);
  ASSERT_TRUE(serialized_public_keyset_handle.ok());
  EXPECT_THAT(VerifyTinkDigitalSignature(kUnsignedMessage, signature_,
                                         *serialized_public_keyset_handle),
              IsOk());
}

TEST_F(VerificationUtilsTest, VerifySignatureWithTink_Fail) {
  absl::StatusOr<std::string> serialized_public_keyset_handle =
      SerializeKeysetWithoutSecretToProtoKeysetFormat(*public_keyset_handle_);
  ASSERT_TRUE(serialized_public_keyset_handle.ok());
  std::string different_unsigned_message =
      "This is not the right unsigned message";
  EXPECT_THAT(VerifyTinkDigitalSignature(different_unsigned_message, signature_,
                                         *serialized_public_keyset_handle),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace oak::crypto::tink
