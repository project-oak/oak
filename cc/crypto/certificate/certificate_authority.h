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

#ifndef CC_CRYPTO_CERTIFICATE_CERTIFICATE_AUTHORITY_H_
#define CC_CRYPTO_CERTIFICATE_CERTIFICATE_AUTHORITY_H_

#include <cstdint>
#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "cc/crypto/certificate/utils.h"
#include "cc/crypto/signing_key.h"
#include "proto/crypto/certificate.pb.h"
#include "proto/crypto/crypto.pb.h"

namespace oak::crypto {

class CertificateAuthority {
 public:
  explicit CertificateAuthority(std::unique_ptr<SigningKeyHandle> signer,
                                std::unique_ptr<Clock> clock)
      : signer_(std::move(signer)), clock_(std::move(clock)) {}

  absl::StatusOr<oak::crypto::v1::Certificate> GenerateCertificate(
      absl::string_view subject_public_key, absl::string_view purpose_id,
      absl::Duration validity_duration) {
    return GenerateCertificate(subject_public_key, purpose_id,
                               validity_duration, nullptr);
  }

  absl::StatusOr<oak::crypto::v1::Certificate> GenerateCertificate(
      absl::string_view subject_public_key, absl::string_view purpose_id,
      absl::Duration validity_duration,
      oak::crypto::v1::ProofOfFreshness* proof_of_freshness_nullable);

 private:
  std::unique_ptr<SigningKeyHandle> signer_;
  std::unique_ptr<Clock> clock_;
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_CERTIFICATE_CERTIFICATE_AUTHORITY_H_
