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
namespace {}  // namespace

absl::StatusOr<CoseSign1> CoseSign1::Deserialize(const std::vector<uint8_t>& data) {
  auto [item, end, error] = cppbor::parse(data);
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't parse COSE Sign1: ", error));
  }
  if (item->type() != cppbor::ARRAY) {
    return UnexpectedCborTypeError("COSE Sign1", cppbor::ARRAY, item->type());
  }
  const cppbor::Array* array = item->asArray();
  if (array->size() != 4) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE Sign1 CBOR array size, expected 4, found ", array->size()));
  }

  const std::unique_ptr<cppbor::Item>& protected_headers = array->get(0);
  if (protected_headers->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("protected_headers", cppbor::BSTR, protected_headers->type());
  }
  const std::unique_ptr<cppbor::Item>& unprotected_headers = array->get(1);
  if (unprotected_headers->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("unprotected_headers", cppbor::MAP, unprotected_headers->type());
  }
  const std::unique_ptr<cppbor::Item>& payload = array->get(2);
  if (payload->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("payload", cppbor::BSTR, payload->type());
  }
  const std::unique_ptr<cppbor::Item>& signature = array->get(3);
  if (signature->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("signature", cppbor::BSTR, signature->type());
  }

  // return CoseSign1 {
  //   .protected_headers = protected_headers->asBstr(),
  //   .unprotected_headers = unprotected_headers->asMap(),
  //   .payload = payload->asBstr(),
  //   .signature = signature->asBstr(),
  //   .item_ = item,
  // };

  return CoseSign1(protected_headers->asBstr(), unprotected_headers->asMap(), payload->asBstr(),
                   signature->asBstr(), std::move(item));
}

absl::StatusOr<CoseKey> CoseKey::Deserialize(const std::vector<uint8_t>& data) {
  auto [item, end, error] = cppbor::parse(data);
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't parse COSE Key: ", error));
  }
  if (item->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("COSE Key", cppbor::MAP, item->type());
  }
  const cppbor::Map* map = item->asMap();
  if (map->size() < 5) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid COSE Key CBOR map size, expected >= 5, found ", map->size()));
  }

  const std::unique_ptr<cppbor::Item>& kty = map->get<int, int>(KTY);
  if (!kty) {
    return absl::InvalidArgumentError("KTY not found");
  }
  if (kty->type() != cppbor::UINT) {
    return UnexpectedCborTypeError("KTY", cppbor::UINT, kty->type());
  }
  const std::unique_ptr<cppbor::Item>& kid = map->get<int, int>(KID);
  if (!kid) {
    return absl::InvalidArgumentError("KID not found");
  }
  if (kid->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("KID", cppbor::BSTR, kid->type());
  }
  const std::unique_ptr<cppbor::Item>& alg = map->get<int, int>(ALG);
  if (!alg) {
    return absl::InvalidArgumentError("ALG not found");
  }
  if (alg->type() != cppbor::NINT) {
    return UnexpectedCborTypeError("ALG", cppbor::NINT, alg->type());
  }
  const std::unique_ptr<cppbor::Item>& key_ops = map->get<int, int>(KEY_OPS);
  if (!key_ops) {
    return absl::InvalidArgumentError("KEY_OPS not found");
  }
  if (key_ops->type() != cppbor::ARRAY) {
    return UnexpectedCborTypeError("key_ops", cppbor::ARRAY, key_ops->type());
  }
  // const std::unique_ptr<cppbor::Item>& base_iv = map->get<int, int>(BASE_IV);
  // if (!base_iv) {
  //   return absl::InvalidArgumentError("BASE_IV not found");
  // }
  // if (base_iv->type() != cppbor::BSTR) {
  //   return UnexpectedCborTypeError("BASE_IV", cppbor::BSTR, base_iv->type());
  // }

  const std::unique_ptr<cppbor::Item>& crv = map->get<int, int>(CRV);
  if (!crv) {
    return absl::InvalidArgumentError("CRV not found");
  }
  if (crv->type() != cppbor::UINT) {
    return UnexpectedCborTypeError("CRV", cppbor::UINT, crv->type());
  }
  const std::unique_ptr<cppbor::Item>& x = map->get<int, int>(X);
  if (!x) {
    return absl::InvalidArgumentError("X not found");
  }
  if (x->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("X", cppbor::BSTR, x->type());
  }
  // const std::unique_ptr<cppbor::Item>& y = map->get<int, int>(Y);
  // if (!y) {
  //   return absl::InvalidArgumentError("Y not found");
  // }
  // if (y->type() != cppbor::BSTR) {
  //   return UnexpectedCborTypeError("Y", cppbor::BSTR, y->type());
  // }

  return CoseKey(kty->asUint(), kid->asBstr(), alg->asNint(),
                 key_ops->asArray(), /*base_vi->asBstr(),*/
                 crv->asUint(), x->asBstr(), nullptr, /*y->asBstr(),*/ std::move(item));
}

const std::vector<uint8_t>& CoseKey::GetPublicKey() const { return x->value(); }

}  // namespace oak::attestation
