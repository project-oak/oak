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
#include "cc/attestation/cose.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::attestation {
namespace {

absl::Status UnexpectedTypeError(std::string_view name, cppbor::MajorType expected, cppbor::MajorType found) {
  return absl::InvalidArgumentError(
      absl::StrCat("expected ", name, " to be a", CborTypeToString(expected), " CBOR type, found ", CborTypeToString(found)));
}

}  // namespace

absl::StatusOr<CoseSign1> CoseSign1::Deserialize(const std::vector<uint8_t>& data) {
  auto [item, end, error] = cppbor::parse(data);
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't parse COSE Sign1: ", error));
  }
  if (item->type() != cppbor::ARRAY) {
    return UnexpectedTypeError("COSE Sign1", cppbor::ARRAY, item->type());
  }
  const cppbor::Array* array = item->asArray();
  if (array->size() != 4) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE Sign1 CBOR array size, expected 4, found ", array->size()));
  }

  const std::unique_ptr<cppbor::Item>& protected_headers = array->get(0);
  if (protected_headers->type() != cppbor::BSTR) {
    return UnexpectedTypeError("protected_headers", cppbor::BSTR, protected_headers->type());
  }
  const std::unique_ptr<cppbor::Item>& unprotected_headers = array->get(1);
  if (unprotected_headers->type() != cppbor::MAP) {
    return UnexpectedTypeError("unprotected_headers", cppbor::MAP, unprotected_headers->type());
  }
  const std::unique_ptr<cppbor::Item>& payload = array->get(2);
  if (payload->type() != cppbor::BSTR) {
    return UnexpectedTypeError("payload", cppbor::BSTR, payload->type());
  }
  const std::unique_ptr<cppbor::Item>& signature = array->get(3);
  if (signature->type() != cppbor::BSTR) {
    return UnexpectedTypeError("signature", cppbor::BSTR, signature->type());
  }

  return CoseSign1 {
    .protected_headers = protected_headers->asBstr(),
    .unprotected_headers = unprotected_headers->asMap(),
    .payload = payload->asBstr(),
    .signature = signature->asBstr(),
  };
}

absl::StatusOr<CoseKey> CoseKey::Deserialize(const std::vector<uint8_t>& data) {
  auto [item, end, error] = cppbor::parse(data);
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't parse COSE Key: ", error));
  }
  if (item->type() != cppbor::MAP) {
    return UnexpectedTypeError("COSE Key", cppbor::MAP, item->type());
  }
  const cppbor::Map* map = item->asMap();
  if (map->size() < 5) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE Key CBOR array size, expected >= 5, found ", map->size()));
  }

  const std::unique_ptr<cppbor::Item>& kty = map->get<int, int>(KTY);
  if (kty->type() != cppbor::UINT) {
    return UnexpectedTypeError("kty", cppbor::UINT, kty->type());
  }
  const std::unique_ptr<cppbor::Item>& kid = map->get<int, int>(KID);
  if (kid->type() != cppbor::BSTR) {
    return UnexpectedTypeError("kid", cppbor::BSTR, kid->type());
  }
  const std::unique_ptr<cppbor::Item>& alg = map->get<int, int>(ALG);
  if (alg->type() != cppbor::UINT) {
    return UnexpectedTypeError("alg", cppbor::UINT, alg->type());
  }
  const std::unique_ptr<cppbor::Item>& key_ops = map->get<int, int>(KEY_OPS);
  if (key_ops->type() != cppbor::UINT) {
    return UnexpectedTypeError("key_ops", cppbor::UINT, key_ops->type());
  }
  const std::unique_ptr<cppbor::Item>& base_vi = map->get<int, int>(BASE_IV);
  if (base_vi->type() != cppbor::BSTR) {
    return UnexpectedTypeError("base_vi", cppbor::BSTR, base_vi->type());
  }

  const std::unique_ptr<cppbor::Item>& crv = map->get<int, int>(CRV);
  if (crv->type() != cppbor::BSTR) {
    return UnexpectedTypeError("crv", cppbor::BSTR, crv->type());
  }
  const std::unique_ptr<cppbor::Item>& x = map->get<int, int>(X);
  if (x->type() != cppbor::BSTR) {
    return UnexpectedTypeError("x", cppbor::BSTR, x->type());
  }
  const std::unique_ptr<cppbor::Item>& y = map->get<int, int>(Y);
  if (y->type() != cppbor::BSTR) {
    return UnexpectedTypeError("y", cppbor::BSTR, y->type());
  }

  return CoseKey {
    .kty = kty->asUint(),
    .kid = kid->asBstr(),
    .alg = alg->asUint(),
    .key_ops = key_ops->asUint(),
    .base_vi = base_vi->asBstr(),

    .crv = crv->asBstr(),
    .x = x->asBstr(),
    .y = y->asBstr(),
  };
}

}  // namespace oak::attestation
