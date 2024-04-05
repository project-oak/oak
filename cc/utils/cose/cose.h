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

#ifndef CC_UTILS_COSE_COSE_H_
#define CC_UTILS_COSE_COSE_H_

#include <cstdint>
#include <memory>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "libcppbor/include/cppbor/cppbor.h"
#include "libcppbor/include/cppbor/cppbor_parse.h"

namespace oak::utils::cose {

// COSE_Sign1 object.
// <https://datatracker.ietf.org/doc/html/rfc8152#section-4.2>
class CoseSign1 {
 public:
  // Parameters about the current layer that are to be cryptographically
  // protected.
  const cppbor::Bstr* protected_headers;
  // Parameters about the current layer that are not cryptographically
  // protected.
  const cppbor::Map* unprotected_headers;
  // Serialized content to be signed.
  const cppbor::Bstr* payload;
  // Array of signatures. Each signature is represented as a COSE_Signature
  // structure.
  const cppbor::Bstr* signature;

  static absl::StatusOr<CoseSign1> Deserialize(absl::string_view data);

  // Puts payload into a COSE_Sign1 and serializes it.
  // TODO(#4818): This function is currently used for tests only. We need to
  // refactor COSE classes to support both serialization and deserialization.
  static absl::StatusOr<std::vector<uint8_t>> Serialize(
      const std::vector<uint8_t>& payload);

 private:
  // Parsed CBOR item containing COSE_Sign1 object.
  std::unique_ptr<cppbor::Item> item_;

  CoseSign1(const cppbor::Bstr* protected_headers,
            const cppbor::Map* unprotected_headers, const cppbor::Bstr* payload,
            const cppbor::Bstr* signature, std::unique_ptr<cppbor::Item>&& item)
      : protected_headers(protected_headers),
        unprotected_headers(unprotected_headers),
        payload(payload),
        signature(signature),
        item_(std::move(item)) {}
};

// COSE_Key object.
// <https://www.rfc-editor.org/rfc/rfc8152#section-7>
class CoseKey {
 public:
  // Identification of the key type.
  const cppbor::Uint* kty;
  // Key usage restriction to this algorithm.
  const cppbor::Nint* alg;
  // Restrict set of permissible operations.
  const cppbor::Array* key_ops;

  // EC identifier.
  const cppbor::Uint* crv;
  // Public key.
  const cppbor::Bstr* x;

  // Deserializes HPKE public key as a COSE_Key.
  // <https://www.rfc-editor.org/rfc/rfc9180.html>
  static absl::StatusOr<CoseKey> DeserializeHpkePublicKey(
      absl::string_view data);
  static absl::StatusOr<CoseKey> DeserializeHpkePublicKey(
      const std::vector<uint8_t>& data);

  // Transforms HPKE public key into a COSE_Key and serializes it.
  // TODO(#4818): This function is currently used for tests only. We need to
  // refactor COSE classes to support both serialization and deserialization.
  static absl::StatusOr<std::vector<uint8_t>> SerializeHpkePublicKey(
      const std::vector<uint8_t>& public_key);

  const std::vector<uint8_t>& GetPublicKey() const { return x->value(); }

 private:
  // COSE Key Common parameters.
  // <https://datatracker.ietf.org/doc/html/rfc8152#section-7.1>
  enum CoseKeyCommonParameter : int {
    KTY = 1,
    KID = 2,
    ALG = 3,
    KEY_OPS = 4,
    BASE_IV = 5,

    // IANA COSE_Key parameters.
    // <https://www.iana.org/assignments/cose/cose.xhtml#key-common-parameters>
    CRV = -1,  // EC identifier.
    X = -2,    // Public key.
  };

  // Key Object parameters.
  // <https://datatracker.ietf.org/doc/html/rfc8152#section-13>
  enum KeyObjectParameter : int {
    Reserved = 0,   // This value is reserved.
    OKP = 1,        // Octet Key Pair.
    EC2 = 2,        // Elliptic Curve Keys with x- and y-coordinate pair.
    Symmetric = 4,  // Symmetric Keys.
  };

  // COSE Algorithms.
  // <https://www.iana.org/assignments/cose/cose.xhtml#algorithms>
  enum CoseAlgorithm : int {
    ES256 = -7,     // ECDSA with SHA-256.
    ECDH_ES = -25,  // ECDH ES with HKDF.
  };

  // Key Operation Values.
  // <https://datatracker.ietf.org/doc/html/rfc8152#section-7.1>
  enum KeyOperationValues : int {
    SIGN = 1,    // The key is used to create signatures.
    VERIFY = 2,  // The key is used for verification of signatures.
  };

  // COSE Elliptic Curve parameters.
  // <https://www.iana.org/assignments/cose/cose.xhtml#elliptic-curves>
  enum CoseEllipticCurveParameter : int {
    P256 = 1,    // NIST P-256 also known as secp256r1.
    X25519 = 4,  // X25519 for use with ECDH only.
  };

  // Parsed CBOR item containing COSE_Key object.
  std::unique_ptr<cppbor::Item> item_;

  CoseKey(const cppbor::Uint* kty, const cppbor::Nint* alg,
          const cppbor::Array* key_ops, const cppbor::Uint* crv,
          const cppbor::Bstr* x, std::unique_ptr<cppbor::Item>&& item)
      : kty(kty),
        alg(alg),
        key_ops(key_ops),
        crv(crv),
        x(x),
        item_(std::move(item)) {}

  static absl::StatusOr<CoseKey> DeserializeHpkePublicKey(
      std::unique_ptr<cppbor::Item>&& item);
};

std::string CborTypeToString(cppbor::MajorType cbor_type);

absl::Status UnexpectedCborTypeError(std::string_view name,
                                     cppbor::MajorType expected,
                                     cppbor::MajorType found);

}  // namespace oak::utils::cose

#endif  // CC_UTILS_COSE_COSE_H_
