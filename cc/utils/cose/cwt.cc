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

#include "cc/utils/cose/cwt.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/cose/cose.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::utils::cose {

absl::StatusOr<Cwt> Cwt::Deserialize(const std::vector<uint8_t>& data) {
  // Deserialize COSE_Sign1.
  absl::StatusOr<CoseSign1> cose_sign1 = CoseSign1::Deserialize(data);
  if (!cose_sign1.ok()) {
    return cose_sign1.status();
  }

  // Deserialize COSE_Sign1 payload.
  auto [item, end, error] = cppbor::parse(cose_sign1->payload->value());
  if (!error.empty()) {
    return absl::InvalidArgumentError(absl::StrCat("couldn't deserialize CWT: ", error));
  }
  if (item->type() != cppbor::MAP) {
    return UnexpectedCborTypeError("CWT", cppbor::ARRAY, item->type());
  }
  const cppbor::Map* map = item->asMap();
  if (map->size() < 3) {
    return absl::InvalidArgumentError(
        absl::StrCat("invalid CWT map size, expected >= 3, found ", map->size()));
  }

  // Get CWT claims.
  auto& iss = map->get<int, int>(ISS);
  if (iss == nullptr) {
    return absl::InvalidArgumentError("ISS not found");
  }
  if (iss->type() != cppbor::TSTR) {
    return UnexpectedCborTypeError("iss", cppbor::TSTR, iss->type());
  }
  auto& sub = map->get<int, int>(SUB);
  if (sub == nullptr) {
    return absl::InvalidArgumentError("SUB not found");
  }
  if (sub->type() != cppbor::TSTR) {
    return UnexpectedCborTypeError("sub", cppbor::TSTR, sub->type());
  }
  auto& subject_public_key_item = map->get<int, int>(SUBJECT_PUBLIC_KEY_ID);
  if (subject_public_key_item == nullptr) {
    return absl::InvalidArgumentError("SUB not found");
  }
  if (subject_public_key_item->type() != cppbor::BSTR) {
    return UnexpectedCborTypeError("SUBJECT_PUBLIC_KEY_ID", cppbor::BSTR,
                                   subject_public_key_item->type());
  }

  // Deserialize COSE_Key.
  absl::StatusOr<CoseKey> subject_public_key =
      CoseKey::DeserializeHpkePublicKey(subject_public_key_item->asBstr()->value());
  if (!subject_public_key.ok()) {
    return subject_public_key.status();
  }

  return Cwt(iss->asTstr(), sub->asTstr(), std::move(*subject_public_key), std::move(item));
}

}  // namespace oak::utils::cose
