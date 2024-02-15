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

namespace {}  // namespace

absl::StatusOr<Cwt> Cwt::Deserialize(const std::vector<uint8_t>& data) {
  // Deserialize COSE Sign1.
  absl::StatusOr<CoseSign1> cose_sign1 = CoseSign1::Deserialize(data);
  if (!cose_sign1.ok()) {
    return cose_sign1.status();
  }
  // if (!cose_sign1->payload) {
  //   return absl::InvalidArgumentError("empty COSE Sign1 payload");
  // }

  std::cerr << "Parsed COSE Sign1" << std::endl;

  // Deserialize COSE Sign1 payload.
  auto [item, end, error] = cppbor::parse(cose_sign1->payload->value());
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't deserialize CWT: ", error));
  }
  // if (item->type() != cppbor::ARRAY) {
  //   return UnexpectedCborTypeError("CWT", cppbor::ARRAY, item->type());
  // }
  // const cppbor::Array* array = item->asArray();
  // if (array->size() != 1) {
  //   return absl::InvalidArgumentError(
  //       absl::StrCat("invalid CWT array size, expected 1, found ", array->size()));
  // }
  // if (array->get(0)->type() != cppbor::MAP) {
  //   return UnexpectedCborTypeError("CWT map", cppbor::MAP, array->get(0)->type());
  // }
  if (item->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("CWT", cppbor::ARRAY, item->type());
  }
  const cppbor::Map* map = item->asMap();
  if (map->size() < 3) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid CWT map size, expected >= 3, found ", map->size()));
  }

  std::cerr << "Deserialized COSE Sign1 payload" << std::endl;

  // Get CWT claims.
  const std::unique_ptr<cppbor::Item>& iss = map->get<int, int>(ISS);
  if (!iss) {
    return absl::InvalidArgumentError("ISS not found");
  }
  if (iss->type() != cppbor::TSTR) {
    return UnexpectedCborTypeError("iss", cppbor::TSTR, iss->type());
  }
  const std::unique_ptr<cppbor::Item>& sub = map->get<int, int>(SUB);
  if (!sub) {
    return absl::InvalidArgumentError("SUB not found");
  }
  if (sub->type() != cppbor::TSTR) {
    return UnexpectedCborTypeError("sub", cppbor::TSTR, sub->type());
  }
  const std::unique_ptr<cppbor::Item>& subject_public_key_item =
      map->get<int, int>(SUBJECT_PUBLIC_KEY_ID);
  if (!subject_public_key_item) {
    return absl::InvalidArgumentError("SUB not found");
  }
  if (subject_public_key_item->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("SUBJECT_PUBLIC_KEY_ID", cppbor::BSTR,
                                   subject_public_key_item->type());
  }
  // const cppbor::Map* subject_public_key_map = subject_public_key_item->asMap();

  std::cerr << "Got CWT claims" << std::endl;

  // Deserialize Cose Key.
  absl::StatusOr<CoseKey> subject_public_key =
      CoseKey::Deserialize(subject_public_key_item->asBstr()->value());
  // absl::StatusOr<CoseKey> subject_public_key = CoseKey::Deserialize(subject_public_key_map);
  if (!subject_public_key.ok()) {
    return subject_public_key.status();
  }

  std::cerr << "Deserialized Cose Key" << std::endl;

  return Cwt{
      .iss = iss->asTstr(),
      .sub = sub->asTstr(),
      .subject_public_key = std::move(*subject_public_key),
  };
}

// absl::StatusOr<std::string>
// ExtractPublicKeyFromCwtCertificate(const std::vector<uint8_t>& certificate) {
// }

}  // namespace oak::attestation
