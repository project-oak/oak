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
arguement with the keyset, and then writes the following to 3 separate files:

1) The message that was signed.
2) The signature.
3) The Tink public keyset in proto serialized format.

The primary objective is to obtain testdata for Tink signature verification
testing.
*/

#include <fstream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/check.h"
#include "absl/log/initialize.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "tink/config/global_registry.h"
#include "tink/configuration.h"
#include "tink/keyset_handle.h"
#include "tink/proto_keyset_format.h"
#include "tink/public_key_sign.h"
#include "tink/signature/signature_config.h"
#include "tink/signature/signature_key_templates.h"

ABSL_FLAG(std::string, message_to_sign, "", "Message for the keyset to sign");
ABSL_FLAG(std::string, public_keyset_filename, "public_keyset",
          "File name to write the public keyset to");
ABSL_FLAG(std::string, signature_filename, "signature",
          "File name to write the signed message to");
ABSL_FLAG(std::string, message_filename, "message",
          "File name to write the original message to");

using ::crypto::tink::ConfigGlobalRegistry;
using ::crypto::tink::Configuration;
using ::crypto::tink::KeyGenConfigGlobalRegistry;
using ::crypto::tink::KeysetHandle;
using ::crypto::tink::PublicKeySign;
using ::crypto::tink::SerializeKeysetToProtoKeysetFormat;
using ::crypto::tink::SerializeKeysetWithoutSecretToProtoKeysetFormat;
using ::crypto::tink::SignatureConfig;
using ::crypto::tink::SignatureKeyTemplates;

namespace {

// Writes `contents` to `filename`. If a file with that name alread exists, it
// will get overwritten.
void WriteContentsToFile(absl::string_view contents, std::string& filename) {
  std::ofstream file;
  file.open(filename);
  file << contents;
  file.close();
}

}  // namespace

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  absl::InitializeLog();

  std::string message_to_sign = absl::GetFlag(FLAGS_message_to_sign);
  std::string public_keyset_filename =
      absl::GetFlag(FLAGS_public_keyset_filename);
  std::string signature_filename = absl::GetFlag(FLAGS_signature_filename);
  std::string message_filename = absl::GetFlag(FLAGS_message_filename);

  QCHECK(!message_to_sign.empty()) << "Must supply a message to sign";
  QCHECK(!public_keyset_filename.empty())
      << "Must supply a file name to write the public keyset to";
  QCHECK(!signature_filename.empty())
      << "Must supply a file name to write the signed message to";
  QCHECK(!message_filename.empty())
      << "Must supply a file name to write the message to";

  // Create a keyset handle.
  absl::Status signature_registry = SignatureConfig::Register();
  CHECK_OK(signature_registry);
  absl::StatusOr<std::unique_ptr<KeysetHandle>> keyset_handle =
      KeysetHandle::GenerateNew(SignatureKeyTemplates::EcdsaP256(),
                                KeyGenConfigGlobalRegistry());
  CHECK_OK(keyset_handle);

  // Sign the message.
  absl::StatusOr<std::unique_ptr<PublicKeySign>> public_key_sign =
      (*keyset_handle)->GetPrimitive<PublicKeySign>(ConfigGlobalRegistry());
  CHECK_OK(public_key_sign);

  absl::StatusOr<std::string> signature =
      (*public_key_sign)->Sign(message_to_sign);
  CHECK_OK(signature);

  // Get public keyset handle. This should be used for verification.
  //
  // https://developers.google.com/tink/faq/registration_errors#case_2_the_error_lists_a_key_type_and_a_primitive
  absl::StatusOr<std::unique_ptr<KeysetHandle>> public_keyset_handle =
      (*keyset_handle)->GetPublicKeysetHandle(KeyGenConfigGlobalRegistry());
  CHECK_OK(public_keyset_handle);

  absl::StatusOr<std::string> serialized_public_keyset_handle =
      SerializeKeysetWithoutSecretToProtoKeysetFormat(**public_keyset_handle);
  CHECK_OK(serialized_public_keyset_handle);

  WriteContentsToFile(message_to_sign, message_filename);
  WriteContentsToFile(*signature, signature_filename);
  WriteContentsToFile(*serialized_public_keyset_handle, public_keyset_filename);

  return 0;
}
