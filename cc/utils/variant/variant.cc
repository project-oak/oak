/*
 * Copyright 2025 The Project Oak Authors
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

#include "cc/utils/variant/variant.h"

#include <optional>
#include <string>

#include "absl/log/check.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/string_view.h"
#include "cc/utils/variant/uuids.h"
#include "proto/attestation/endorsement.pb.h"

namespace oak {
namespace {

using ::oak::attestation::v1::AmdSevSnpEndorsement;
using ::oak::attestation::v1::ApplicationEndorsement;
using ::oak::attestation::v1::ContainerEndorsement;
using ::oak::attestation::v1::FirmwareEndorsement;
using ::oak::attestation::v1::KernelEndorsement;
using ::oak::attestation::v1::SystemEndorsement;

std::string RawUuid(absl::string_view uuidHex) {
  std::string strip = absl::StrReplaceAll(uuidHex, {{"-", ""}});
  std::string raw;
  CHECK(absl::HexStringToBytes(strip, &raw));
  CHECK_EQ(raw.length(), 16u);  // 128 bits
  return raw;
}

template <typename T>
Variant CreateVariant(absl::string_view uuidHex, const T& message) {
  std::string serialized;
  CHECK(message.SerializeToString(&serialized));

  Variant variant;
  variant.set_id(RawUuid(uuidHex));
  variant.set_value(serialized);
  return variant;
}

template <typename T>
std::optional<T> ParseVariant(absl::string_view uuidHex,
                              const Variant& variant) {
  if (RawUuid(uuidHex) != variant.id()) {
    return std::nullopt;
  }

  T message;
  message.ParseFromString(variant.value());
  return message;
}

}  // namespace

template <>
Variant ToVariant<AmdSevSnpEndorsement>(const AmdSevSnpEndorsement& message) {
  return CreateVariant(internal::kAmdSevSnpPlatformEndorsementUuid, message);
}

template <>
Variant ToVariant<FirmwareEndorsement>(const FirmwareEndorsement& message) {
  return CreateVariant(internal::kFirmwareEndorsementUuid, message);
}

template <>
Variant ToVariant<KernelEndorsement>(const KernelEndorsement& message) {
  return CreateVariant(internal::kKernelEndorsementUuid, message);
}

template <>
Variant ToVariant<SystemEndorsement>(const SystemEndorsement& message) {
  return CreateVariant(internal::kSystemEndorsementUuid, message);
}

template <>
Variant ToVariant<ContainerEndorsement>(const ContainerEndorsement& message) {
  return CreateVariant(internal::kContainerEndorsementUuid, message);
}

template <>
Variant ToVariant<ApplicationEndorsement>(
    const ApplicationEndorsement& message) {
  return CreateVariant(internal::kApplicationEndorsementUuid, message);
}

template <>
std::optional<AmdSevSnpEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<AmdSevSnpEndorsement>(
      internal::kAmdSevSnpPlatformEndorsementUuid, variant);
}

template <>
std::optional<FirmwareEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<FirmwareEndorsement>(internal::kFirmwareEndorsementUuid,
                                           variant);
}

template <>
std::optional<KernelEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<KernelEndorsement>(internal::kKernelEndorsementUuid,
                                         variant);
}

template <>
std::optional<SystemEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<SystemEndorsement>(internal::kSystemEndorsementUuid,
                                         variant);
}

template <>
std::optional<ContainerEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<ContainerEndorsement>(internal::kContainerEndorsementUuid,
                                            variant);
}

template <>
std::optional<ApplicationEndorsement> FromVariant(const Variant& variant) {
  return ParseVariant<ApplicationEndorsement>(
      internal::kApplicationEndorsementUuid, variant);
}

}  // namespace oak
