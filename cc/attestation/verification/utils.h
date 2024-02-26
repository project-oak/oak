/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_ATTESTATION_VERIFICATION_UTILS_H_
#define CC_ATTESTATION_VERIFICATION_UTILS_H_

#include <string>

#include "absl/status/statusor.h"
#include "proto/attestation/evidence.pb.h"

namespace oak::attestation::verification {

absl::StatusOr<std::string> ExtractEncryptionPublicKey(
    const ::oak::attestation::v1::Evidence& evidence);

absl::StatusOr<std::string> ExtractSigningPublicKey(
    const ::oak::attestation::v1::Evidence& evidence);

}  // namespace oak::attestation::verification

#endif  // CC_ATTESTATION_VERIFICATION_ATTESTATION_VERIFIER_H_
