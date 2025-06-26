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

#include "cc/crypto/certificate/certificate_authority.h"

#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "cc/crypto/certificate/utils.h"
#include "cc/crypto/signing_key.h"
#include "google/protobuf/timestamp.pb.h"
#include "proto/crypto/certificate.pb.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/validity.pb.h"

namespace oak::crypto {

namespace {
using google::protobuf::Timestamp;
using ::oak::Validity;
using ::oak::crypto::v1::Certificate;
using ::oak::crypto::v1::CertificatePayload;
using ::oak::crypto::v1::ProofOfFreshness;
using ::oak::crypto::v1::Signature;
using ::oak::crypto::v1::SignatureInfo;
using ::oak::crypto::v1::SubjectPublicKeyInfo;
}  // namespace

absl::StatusOr<Certificate> CertificateAuthority::GenerateCertificate(
    absl::string_view subject_public_key, absl::string_view purpose_id,
    absl::Duration validity_duration,
    ProofOfFreshness* proof_of_freshness_nullable) {
  // Set certificate validity.
  const absl::Time not_before = clock_->CurrentTime();
  const absl::Time not_after = not_before + validity_duration;

  absl::StatusOr<Timestamp> not_before_timestamp = ToTimestamp(not_before);
  if (!not_before_timestamp.ok()) {
    return not_before_timestamp.status();
  }
  absl::StatusOr<Timestamp> not_after_timestamp = ToTimestamp(not_after);
  if (!not_after_timestamp.ok()) {
    return not_after_timestamp.status();
  }

  Validity validity;
  *validity.mutable_not_before() = *not_before_timestamp;
  *validity.mutable_not_after() = *not_after_timestamp;

  // Prepare the certificate payload.
  SubjectPublicKeyInfo subject_public_key_info;
  subject_public_key_info.set_public_key(subject_public_key);
  subject_public_key_info.set_purpose_id(purpose_id);

  CertificatePayload certificate_payload;
  *certificate_payload.mutable_validity() = validity;
  *certificate_payload.mutable_subject_public_key_info() =
      subject_public_key_info;

  if (proof_of_freshness_nullable != nullptr) {
    *certificate_payload.mutable_proof_of_freshness() =
        *proof_of_freshness_nullable;
  }

  std::string serialized_certificate_payload =
      certificate_payload.SerializeAsString();
  if (serialized_certificate_payload.empty()) {
    return absl::InternalError("couldn't serialize certificate payload");
  }

  // Sign the certificate.
  absl::StatusOr<Signature> signature =
      signer_->Sign(serialized_certificate_payload);
  if (!signature.ok()) {
    return signature.status();
  }
  SignatureInfo signature_info;
  signature_info.set_signature(signature->signature());

  Certificate certificate;
  certificate.set_serialized_payload(serialized_certificate_payload);
  *certificate.mutable_signature_info() = signature_info;

  return certificate;
}

}  // namespace oak::crypto
