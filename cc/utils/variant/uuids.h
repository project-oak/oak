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

#ifndef CC_UTILS_VARIANT_UUIDS_H_
#define CC_UTILS_VARIANT_UUIDS_H_

#include "absl/strings/string_view.h"

namespace oak {
namespace internal {

constexpr absl::string_view kAmdSevSnpPlatformEndorsementUuid =
    "5a12d00f-48a0-4224-bff4-975c7657438f";
constexpr absl::string_view kFirmwareEndorsementUuid =
    "de4a0d55-60ea-4dc6-abd1-09ed744f80ea";
constexpr absl::string_view kKernelEndorsementUuid =
    "89511d65-5d35-4601-900b-1e6dbaf842b6";
constexpr absl::string_view kSystemEndorsementUuid =
    "4722655d-963d-4fc9-8443-f14571dd32a2";
constexpr absl::string_view kContainerEndorsementUuid =
    "7297a51f-a05d-49a1-afdb-64cdee07862d";
constexpr absl::string_view kApplicationEndorsementUuid =
    "e84ed714-669d-430a-a60f-8a651e5a5503";

}  // namespace internal
}  // namespace oak

#endif  // CC_UTILS_VARIANT_UUIDS_H_
