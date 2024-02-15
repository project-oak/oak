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

#include <memory>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/attestation/cose.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::attestation {

// CBOR Web Token (CWT) claim representing a serialized public key for the certificate.
// <https://www.iana.org/assignments/cwt/cwt.xhtml>
static constexpr int kSubjectPublicKeyId = -4670552;
// static constexpr int kSubjectPublicKeyId = -4670552;

// // Set of custom CBOR Web Token (CWT) claims used by Oak.
// // <https://www.iana.org/assignments/cwt/cwt.xhtml>
// enum CwtClaim : int {
//   CwtClaimSubjectPublicKeyId = -4670552,  // Serialized  public key for this certificate.
// };

namespace {

}  // namespace

absl::StatusOr<Cwt> Cwt::Deserialize(const std::vector<uint8_t>& data) {
  // Deserialize COSE Sign1.
  absl::StatusOr<CoseSign1> cose_sign1 = CoseSign1::Deserialize(data);
  if (!cose_sign1.ok()) {
    return cose_sign1.status();
  }

  // Extract serialized COSE Key from COSE Sign1 payload.
  auto [item, end, error] = cppbor::parse(cose_sign1->payload);
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't parse COSE Sign1 payload: ", error));
  }
  if (item->type() != cppbor::MAP) {
    return UnexpectedTypeError("COSE Sign1", cppbor::MAP, item->type());
  }
  const cppbor::Array* array = item->asArray();
  if (array->size() != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE Sign1 payload size, expected 1, found ", array->size()));
  }

  // Deserialize Cose Key.
  absl::StatusOr<CoseKey> cose_key = CoseKey::Deserialize(array->get(0));
  if (!cose_key.ok()) {
    return cose_key.status();
  }

}

// absl::StatusOr<std::string>
// ExtractPublicKeyFromCwtCertificate(const std::vector<uint8_t>& certificate) {
// }

}  // namespace oak::attestation
