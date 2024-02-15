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

#ifndef CC_ATTESTATION_COSE_H_
#define CC_ATTESTATION_COSE_H_

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::attestation {

// COSE Sign1 object.
// <https://datatracker.ietf.org/doc/html/rfc8152#section-4.2>
class CoseSign1 {
 public:
  const cppbor::Bstr* protected_headers;
  const cppbor::Map* unprotected_headers;
  const cppbor::Bstr* payload;
  const cppbor::Bstr* signature;

  CoseSign1(const cppbor::Bstr* protected_headers, const cppbor::Map* unprotected_headers,
            const cppbor::Bstr* payload, const cppbor::Bstr* signature,
            std::unique_ptr<cppbor::Item>&& item)
      : protected_headers(protected_headers),
        unprotected_headers(unprotected_headers),
        payload(payload),
        signature(signature),
        item_(std::move(item)) {}

  static absl::StatusOr<CoseSign1> Deserialize(const std::vector<uint8_t>& data);

 private:
  // Parsed CBOR item containing COSE Sign1 object.
  std::unique_ptr<cppbor::Item> item_;
};

// COSE Key object.
// <https://www.rfc-editor.org/rfc/rfc8152#section-7>
//
// This struct is a wrapper and doesn't take ownership of the corresponding CBOR fields.
// Note: Oak only uses a subset of CBOR keys defined for the COSE Key object.
class CoseKey {
 public:
  const cppbor::Uint* kty;
  const cppbor::Bstr* kid;
  const cppbor::Nint* alg;
  const cppbor::Array* key_ops;
  // const cppbor::Bstr* base_iv;

  const cppbor::Uint* crv;
  const cppbor::Bstr* x;
  const cppbor::Bstr* y;

  CoseKey(const cppbor::Uint* kty, const cppbor::Bstr* kid, const cppbor::Nint* alg,
          const cppbor::Array* key_ops, const cppbor::Uint* crv, const cppbor::Bstr* x,
          const cppbor::Bstr* y, std::unique_ptr<cppbor::Item>&& item)
      : kty(kty),
        kid(kid),
        alg(alg),
        key_ops(key_ops),
        crv(crv),
        x(x),
        y(y),
        item_(std::move(item)) {}

  static absl::StatusOr<CoseKey> Deserialize(const std::vector<uint8_t>& data);

  const std::vector<uint8_t>& GetPublicKey() const;

 private:
  enum Parameter : int {
    KTY = 1,
    KID = 2,
    ALG = 3,
    KEY_OPS = 4,
    BASE_IV = 5,

    // IANA COSE Key parameters.
    // <https://www.iana.org/assignments/cose/cose.xhtml#key-common-parameters>
    CRV = -1,  // EC identifier.
    X = -2,    // X-coordinate.
    Y = -3,    // Y-coordinate.
  };

  // Parsed CBOR item containing COSE Key object.
  std::unique_ptr<cppbor::Item> item_;
};

std::string CborTypeToString(cppbor::MajorType cbor_type) {
  switch (cbor_type) {
    case cppbor::MajorType::UINT:
      return "UINT";
    case cppbor::MajorType::NINT:
      return "NINT";
    case cppbor::MajorType::BSTR:
      return "BSTR";
    case cppbor::MajorType::TSTR:
      return "TSTR";
    case cppbor::MajorType::ARRAY:
      return "ARRAY";
    case cppbor::MajorType::MAP:
      return "MAP";
    case cppbor::MajorType::SEMANTIC:
      return "SEMANTIC";
    case cppbor::MajorType::SIMPLE:
      return "SIMPLE";
    default:
      return absl::StrCat("UNKNOWN(", cbor_type, ")");
  }
}

absl::Status UnexpectedCborTypeError(std::string_view name, cppbor::MajorType expected,
                                     cppbor::MajorType found) {
  return absl::InvalidArgumentError(absl::StrCat("expected ", name, " to have ",
                                                 CborTypeToString(expected), " CBOR type, found ",
                                                 CborTypeToString(found)));
}

// template<typename T> absl::Status CheckCborItemType(const cppbor::Item* item) {
//   if (item->type() == T::kMajorType) {
//     return absl::OkStatus();
//   } else {
//     return absl::InvalidArgumentError(
//         absl::StrCat("expected ", CborTypeToString(T::kMajorType) ," CBOR type, found ",
//         CborTypeToString(item->type())));
//   }
// }

}  // namespace oak::attestation

#endif  // CC_ATTESTATION_COSE_H_
