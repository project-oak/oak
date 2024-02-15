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

#ifndef CC_ATTESTATION_CWT_H_
#define CC_ATTESTATION_CWT_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/attestation/cose.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::attestation {

// CBOR Web Token (CWT).
// <https://datatracker.ietf.org/doc/html/rfc8392>
class Cwt {
 public:
  const cppbor::Tstr* iss;
  const cppbor::Tstr* sub;
  CoseKey subject_public_key;

  Cwt(const cppbor::Tstr* iss, const cppbor::Tstr* sub, CoseKey&& subject_public_key,
      std::unique_ptr<cppbor::Item>&& item)
      : iss(iss),
        sub(sub),
        subject_public_key(std::move(subject_public_key)),
        item_(std::move(item)) {}

  static absl::StatusOr<Cwt> Deserialize(const std::vector<uint8_t>& data);

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

    // Custom Oak claim representing serialized public key for the certificate.
    SUBJECT_PUBLIC_KEY_ID = -4670552,
  };

  // Parsed CBOR item containing CWT object.
  std::unique_ptr<cppbor::Item> item_;
};

}  // namespace oak::attestation

#endif  // CC_ATTESTATION_CWT_H_
