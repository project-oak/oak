/*
 * Copyright 2026 The Project Oak Authors
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

#ifndef CC_CRYPTO_TINK_SIGNATURE_ECDSA_P256_PARAMETERS_H_
#define CC_CRYPTO_TINK_SIGNATURE_ECDSA_P256_PARAMETERS_H_

#include "absl/status/statusor.h"
#include "tink/signature/ecdsa_parameters.h"

namespace oak::crypto::tink {

// Returns ECDSA parameters equivalent to the deprecated
// `SignatureKeyTemplates::EcdsaP256()` key template: NIST P-256 curve, SHA-256
// hash, DER signature encoding and TINK output prefix.
//
// Intended to be passed to `KeysetHandle::GenerateNewFromParameters`.
//
// See
// https://github.com/tink-crypto/tink-cc/blob/v2.7.0/tink/signature/signature_key_templates.cc
absl::StatusOr<::crypto::tink::EcdsaParameters> EcdsaP256Parameters();

}  // namespace oak::crypto::tink

#endif  // CC_CRYPTO_TINK_SIGNATURE_ECDSA_P256_PARAMETERS_H_
