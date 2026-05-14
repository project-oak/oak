/*
 * Copyright 2026 The Project Oak Authors
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

#include "cc/crypto/tink/signature/ml_dsa_44-ffi.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "cc/crypto/tink/signature/ml_dsa_44_utils.h"
#include "cc/ffi/bytes_view.h"
#include "cc/ffi/cxx_string.h"

namespace oak::crypto::tink {

using ::oak::ffi::CxxString;
using ::oak::ffi::bindings::BytesView;

extern "C" {

StatusWrapper MlDsa44Verify(BytesView message, BytesView signature,
                            BytesView raw_public_key) {
  absl::Status status = VerifyMlDsa44(message, signature, raw_public_key);

  StatusWrapper result;
  result.status_code = static_cast<int>(status.code());
  *result.status_message.string() = status.message();
  return result;
}

MlDsa44SignResult MlDsa44Sign(BytesView message, BytesView raw_private_key,
                              BytesView raw_public_key) {
  MlDsa44KeyPair key_pair{
      .public_key = std::string(raw_public_key.data, raw_public_key.len),
      .private_key = std::string(raw_private_key.data, raw_private_key.len),
  };
  absl::StatusOr<std::string> signature = SignMlDsa44(message, key_pair);

  MlDsa44SignResult result;
  result.status_code = static_cast<int>(signature.status().code());
  *result.status_message.string() = signature.status().message();
  if (signature.ok()) {
    *result.signature.string() = *signature;
  }
  return result;
}

MlDsa44KeyGenResult MlDsa44KeyGen() {
  absl::StatusOr<MlDsa44KeyPair> keypair = GenerateMlDsa44KeyPair();

  MlDsa44KeyGenResult result;
  result.status_code = static_cast<int>(keypair.status().code());
  *result.status_message.string() = keypair.status().message();
  if (keypair.ok()) {
    *result.public_key.string() = keypair->public_key;
    *result.private_key.string() = keypair->private_key;
  }
  return result;
}

}  // extern C

}  // namespace oak::crypto::tink
