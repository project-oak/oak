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

/*
This binary creates a random keyset, signs the supplied `message_to_sign`
argument with the keyset, and then writes the following to 3 separate files:

1) The message that was signed.
2) The signature.
3) The certificate for the message that can be used for an endorsement.
4) The Tink public keyset in proto serialized format.

The primary objective is to obtain testdata for Tink signature verification
testing.
*/

#include <fstream>
#include <memory>
#include <string>
#include <utility>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/check.h"
#include "absl/log/initialize.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "cc/crypto/certificate/certificate_authority.h"
#include "cc/crypto/certificate/utils.h"
#include "cc/crypto/signing_key.h"
#include "tink/config/global_registry.h"
#include "tink/keyset_handle.h"
#include "tink/proto_keyset_format.h"
#include "tink/public_key_sign.h"
#include "tink/signature/signature_config.h"
#include "tink/signature/signature_key_templates.h"

ABSL_FLAG(std::string, message_to_sign, "", "Message for the keyset to sign");
ABSL_FLAG(std::string, purpose, "",
          "Message purpose, to use when generating the certificate");
ABSL_FLAG(std::string, public_keyset_filename, "public_keyset",
          "File name to write the public keyset to");
ABSL_FLAG(std::string, signature_filename, "signature",
          "File name to write the signed message to");
ABSL_FLAG(std::string, message_filename, "message",
          "File name to write the original message to");
ABSL_FLAG(std::string, certificate_filename, "certificate",
          "File name to write the certificate to");

using ::absl::GetFlag;
using ::absl::Hours;
using ::absl::InitializeLog;
using ::absl::ParseCommandLine;
using ::absl::Status;
using ::absl::StatusOr;
using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::KeyGenConfigGlobalRegistry;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::PublicKeySign;
using ::crypto::tink::SerializeKeysetWithoutSecretToProtoKeysetFormat;
using ::crypto::tink::SignatureConfig;
using ::crypto::tink::SignatureKeyTemplates;
using ::oak::crypto::CertificateAuthority;
using ::oak::crypto::SigningKeyHandle;
using ::oak::crypto::SystemClock;
using ::oak::crypto::v1::Certificate;
using ::oak::crypto::v1::Signature;

namespace {

// Writes `contents` to `filename`. If a file with that name alread exists, it
// will get overwritten.
void WriteContentsToFile(absl::string_view contents, std::string& filename) {
  std::ofstream file;
  file.open(filename);
  file << contents;
  file.close();
}

class KeysetSigningKeyHandle : public SigningKeyHandle {
 public:
  explicit KeysetSigningKeyHandle(std::unique_ptr<KeysetHandle> keyset_handle)
      : keyset_handle_(std::move(keyset_handle)) {}

  virtual StatusOr<Signature> Sign(absl::string_view message) override {
    StatusOr<std::unique_ptr<PublicKeySign>> public_key_sign =
        keyset_handle_->GetPrimitive<crypto::tink::PublicKeySign>(
            ConfigGlobalRegistry());
    if (!public_key_sign.ok()) {
      return public_key_sign.status();
    }

    StatusOr<std::string> signature_string = (*public_key_sign)->Sign(message);
    if (!signature_string.ok()) {
      return signature_string.status();
    }

    Signature signature;
    signature.set_signature(*signature_string);
    return signature;
  }

 private:
  std::unique_ptr<KeysetHandle> keyset_handle_;
};

}  // namespace

int main(int argc, char** argv) {
  ParseCommandLine(argc, argv);
  InitializeLog();

  std::string message_to_sign = GetFlag(FLAGS_message_to_sign);
  std::string purpose = GetFlag(FLAGS_purpose);
  std::string public_keyset_filename = GetFlag(FLAGS_public_keyset_filename);
  std::string signature_filename = GetFlag(FLAGS_signature_filename);
  std::string message_filename = GetFlag(FLAGS_message_filename);
  std::string certificate_filename = GetFlag(FLAGS_certificate_filename);

  QCHECK(!message_to_sign.empty()) << "Must supply a message to sign";
  QCHECK(!public_keyset_filename.empty())
      << "Must supply a file name to write the public keyset to";
  QCHECK(!signature_filename.empty())
      << "Must supply a file name to write the signed message to";
  QCHECK(!message_filename.empty())
      << "Must supply a file name to write the message to";
  QCHECK(!certificate_filename.empty())
      << "Must supply a file name to write the certificate to";

  // Create a keyset handle.
  Status signature_registry = SignatureConfig::Register();
  CHECK_OK(signature_registry);
  StatusOr<std::unique_ptr<KeysetHandle>> keyset_handle =
      KeysetHandle::GenerateNew(SignatureKeyTemplates::EcdsaP256(),
                                KeyGenConfigGlobalRegistry());
  CHECK_OK(keyset_handle);

  // Get public keyset handle. This should be used for verification.
  //
  // https://developers.google.com/tink/faq/registration_errors#case_2_the_error_lists_a_key_type_and_a_primitive
  StatusOr<std::unique_ptr<KeysetHandle>> public_keyset_handle =
      (*keyset_handle)->GetPublicKeysetHandle(KeyGenConfigGlobalRegistry());
  CHECK_OK(public_keyset_handle);

  // Create a signing key handle.
  std::unique_ptr<SigningKeyHandle> signing_key_handle =
      make_unique<KeysetSigningKeyHandle>(*std::move(keyset_handle));

  // Sign the message.
  StatusOr<Signature> signature = signing_key_handle->Sign(message_to_sign);
  CHECK_OK(signature);

  // Generate the certificate for the message.
  CertificateAuthority certificate_authority(std::move(signing_key_handle),
                                             std::make_unique<SystemClock>());
  StatusOr<Certificate> certificate = certificate_authority.GenerateCertificate(
      message_to_sign, purpose, Hours(100 * 365 * 24));
  CHECK_OK(certificate);

  StatusOr<std::string> serialized_public_keyset_handle =
      SerializeKeysetWithoutSecretToProtoKeysetFormat(**public_keyset_handle);
  CHECK_OK(serialized_public_keyset_handle);

  WriteContentsToFile(message_to_sign, message_filename);
  WriteContentsToFile(signature->signature(), signature_filename);
  WriteContentsToFile(certificate->SerializeAsString(), certificate_filename);
  WriteContentsToFile(*serialized_public_keyset_handle, public_keyset_filename);

  return 0;
}
