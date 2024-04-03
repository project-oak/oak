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

#include "cc/utils/cose/cose.h"

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::utils::cose {

absl::StatusOr<CoseSign1> CoseSign1::Deserialize(absl::string_view data) {
  auto [item, end, error] =
      cppbor::parse(reinterpret_cast<const uint8_t*>(data.data()), data.size());
  if (!error.empty()) {
    return absl::InvalidArgumentError(
        absl::StrCat("couldn't parse COSE_Sign1: ", error));
  }
  if (item->type() != cppbor::ARRAY) {
    return UnexpectedCborTypeError("COSE_Sign1", cppbor::ARRAY, item->type());
  }
  const cppbor::Array* array = item->asArray();
  if (array->size() != 4) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE_Sign1 CBOR array size, expected 4, found ",
                     array->size()));
  }

  const auto& protected_headers = array->get(0);
  if (protected_headers->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("protected_headers", cppbor::BSTR,
                                   protected_headers->type());
  }
  const auto& unprotected_headers = array->get(1);
  if (unprotected_headers->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("unprotected_headers", cppbor::MAP,
                                   unprotected_headers->type());
  }
  const auto& payload = array->get(2);
  if (payload->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("payload", cppbor::BSTR, payload->type());
  }
  const auto& signature = array->get(3);
  if (signature->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("signature", cppbor::BSTR,
                                   signature->type());
  }

  return CoseSign1(protected_headers->asBstr(), unprotected_headers->asMap(),
                   payload->asBstr(), signature->asBstr(), std::move(item));
}

absl::StatusOr<std::vector<uint8_t>> CoseSign1::Serialize(
    const std::vector<uint8_t>& payload) {
  cppbor::Array array;
  // TODO(#4818): Implement headers and signature.
  std::vector<uint8_t> protected_headers;
  std::vector<uint8_t> signature;
  array.add(cppbor::Bstr(protected_headers));
  array.add(cppbor::Map());
  array.add(cppbor::Bstr(payload));
  array.add(cppbor::Bstr(signature));

  std::vector<uint8_t> encoded_array(array.encodedSize());
  array.encode(encoded_array.data(),
               encoded_array.data() + encoded_array.size());
  return encoded_array;
}

absl::StatusOr<CoseKey> CoseKey::DeserializeHpkePublicKey(
    absl::string_view data) {
  auto [item, end, error] =
      cppbor::parse(reinterpret_cast<const uint8_t*>(data.data()), data.size());
  if (!error.empty()) {
    return absl::InvalidArgumentError(
        absl::StrCat("couldn't parse COSE_Key: ", error));
  }
  return DeserializeHpkePublicKey(std::move(item));
}

absl::StatusOr<CoseKey> CoseKey::DeserializeHpkePublicKey(
    const std::vector<uint8_t>& data) {
  auto [item, end, error] = cppbor::parse(data);
  if (!error.empty()) {
    return absl::InvalidArgumentError(
        absl::StrCat("couldn't parse COSE_Key: ", error));
  }
  return DeserializeHpkePublicKey(std::move(item));
}

absl::StatusOr<CoseKey> CoseKey::DeserializeHpkePublicKey(
    std::unique_ptr<cppbor::Item>&& item) {
  if (item->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("COSE_Key", cppbor::MAP, item->type());
  }
  const cppbor::Map* map = item->asMap();
  if (map->size() < 5) {
    return absl::InvalidArgumentError(absl::StrCat(
        "invalid COSE_Key CBOR map size, expected >= 5, found ", map->size()));
  }

  const auto& kty = map->get<int, int>(KTY);
  if (kty == nullptr) {
    return absl::InvalidArgumentError("KTY not found");
  }
  if (kty->type() != cppbor::UINT) {
    return UnexpectedCborTypeError("KTY", cppbor::UINT, kty->type());
  }
  const auto& alg = map->get<int, int>(ALG);
  if (alg == nullptr) {
    return absl::InvalidArgumentError("ALG not found");
  }
  if (alg->type() != cppbor::NINT) {
    return UnexpectedCborTypeError("ALG", cppbor::NINT, alg->type());
  }
  const auto& key_ops = map->get<int, int>(KEY_OPS);
  if (key_ops == nullptr) {
    return absl::InvalidArgumentError("KEY_OPS not found");
  }
  if (key_ops->type() != cppbor::ARRAY) {
    return UnexpectedCborTypeError("key_ops", cppbor::ARRAY, key_ops->type());
  }

  const auto& crv = map->get<int, int>(CRV);
  if (crv == nullptr) {
    return absl::InvalidArgumentError("CRV not found");
  }
  if (crv->type() != cppbor::UINT) {
    return UnexpectedCborTypeError("CRV", cppbor::UINT, crv->type());
  }
  const auto& x = map->get<int, int>(X);
  if (x == nullptr) {
    return absl::InvalidArgumentError("X not found");
  }
  if (x->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("X", cppbor::BSTR, x->type());
  }

  return CoseKey(kty->asUint(), alg->asNint(), key_ops->asArray(),
                 crv->asUint(), x->asBstr(), std::move(item));
}

absl::StatusOr<std::vector<uint8_t>> CoseKey::SerializeHpkePublicKey(
    const std::vector<uint8_t>& public_key) {
  cppbor::Map map;
  map.add(KTY, cppbor::Uint(OKP));
  map.add(ALG, cppbor::Nint(ECDH_ES));
  // TODO(#4818): Add correct key ops.
  map.add(KEY_OPS, cppbor::Array());
  map.add(CRV, cppbor::Uint(X25519));
  map.add(X, cppbor::Bstr(public_key));

  std::vector<uint8_t> encoded_map(map.encodedSize());
  map.encode(encoded_map.data(), encoded_map.data() + encoded_map.size());
  return encoded_map;
}

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

absl::Status UnexpectedCborTypeError(std::string_view name,
                                     cppbor::MajorType expected,
                                     cppbor::MajorType found) {
  return absl::InvalidArgumentError(
      absl::StrCat("expected ", name, " to have ", CborTypeToString(expected),
                   " CBOR type, found ", CborTypeToString(found)));
}

}  // namespace oak::utils::cose
