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

#ifndef CC_UTILS_COSE_CWT_H_
#define CC_UTILS_COSE_CWT_H_

#include <cstdint>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/cose/cose.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::utils::cose {

// CBOR Web Token (CWT).
// <https://datatracker.ietf.org/doc/html/rfc8392>
class Cwt {
 public:
  const cppbor::Tstr* iss;
  const cppbor::Tstr* sub;
  // Public key associated with the subject in the form of a COSE_Key structure.
  CoseKey subject_public_key;

  static absl::StatusOr<Cwt> Deserialize(absl::string_view data);

  // Transforms HPKE public key into a CWT and serializes it.
  // TODO(#4818): This function is currently used for tests only. We need to
  // refactor CWT class to support both serialization and deserialization.
  static absl::StatusOr<std::vector<uint8_t>> SerializeHpkePublicKey(
      const std::vector<uint8_t>& public_key);

 private:
  // CBOR map keys.
  // <https://datatracker.ietf.org/doc/html/rfc8392#section-4>
  enum Key : int {
    ISS = 1,
    SUB = 2,
    AUD = 3,
    EXP = 4,
    NBF = 5,
    IAT = 6,
    CTI = 7,

    // Public key associated with the subject in the form of a COSE_Key
    // structure.
    // <https://pigweed.googlesource.com/open-dice/+/refs/heads/main/docs/specification.md#cbor-uds-certificates>
    SUBJECT_PUBLIC_KEY_ID = -4670552,
  };

  // Parsed CBOR item containing CWT object.
  std::unique_ptr<cppbor::Item> item_;

  Cwt(const cppbor::Tstr* iss, const cppbor::Tstr* sub,
      CoseKey&& subject_public_key, std::unique_ptr<cppbor::Item>&& item)
      : iss(iss),
        sub(sub),
        subject_public_key(std::move(subject_public_key)),
        item_(std::move(item)) {}
};

}  // namespace oak::utils::cose

#endif  // CC_UTILS_COSE_CWT_H_
