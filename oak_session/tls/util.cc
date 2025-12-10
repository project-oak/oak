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

#include <cstdio>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "openssl/base.h"
#include "openssl/ssl.h"

namespace oak::session::tls::util {

absl::StatusOr<std::string> LoadPrivateKeyFromFile(const char* key_path) {
  FILE* file = fopen(key_path, "r");
  if (file == nullptr) {
    return absl::InternalError("Failed to open private key file");
  }
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_PrivateKey(file, nullptr, nullptr, nullptr));
  fclose(file);
  if (pkey == nullptr) {
    return absl::InternalError("Failed to read private key from file");
  }

  int der_len = i2d_PrivateKey(pkey.get(), NULL);
  if (der_len < 0) {
    return absl::InternalError("Failed to get DER length from certificate");
  }

  std::string pkey_der;
  pkey_der.resize(der_len);
  unsigned char* p = reinterpret_cast<unsigned char*>(pkey_der.data());

  der_len = i2d_PrivateKey(pkey.get(), &p);
  if (der_len < 0) {
    return absl::InternalError("Failed to convert certificate to DER");
  }

  return pkey_der;
}

absl::StatusOr<std::string> LoadCertificateFromFile(const char* cert_path) {
  FILE* file = fopen(cert_path, "r");
  if (file == nullptr) {
    return absl::InternalError("Failed to open certificate file");
  }
  bssl::UniquePtr<X509> cert(PEM_read_X509(file, nullptr, nullptr, nullptr));
  fclose(file);
  if (cert == nullptr) {
    return absl::InternalError("Failed to read certificate from file");
  }

  int der_len = i2d_X509(cert.get(), nullptr);
  if (der_len < 0) {
    return absl::InternalError("Failed to get DER length from certificate");
  }

  std::string cert_der;
  cert_der.resize(der_len);
  unsigned char* p = reinterpret_cast<unsigned char*>(cert_der.data());

  der_len = i2d_X509(cert.get(), &p);
  if (der_len < 0) {
    return absl::InternalError("Failed to convert certificate to DER");
  }

  return cert_der;
}

}  // namespace oak::session::tls::util
