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

#include "oak_session/tls/util.h"

#include <cstdio>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "openssl/base.h"
#include "openssl/ec.h"
#include "openssl/evp.h"
#include "openssl/obj.h"
#include "openssl/ssl.h"
#include "openssl/x509.h"

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

class StaticCertIdentityProvider : public TlsIdentityProvider {
 public:
  StaticCertIdentityProvider(TlsIdentity identity)
      : identity_(std::move(identity)) {}

  absl::StatusOr<TlsIdentity> GetIdentity() override { return identity_; }

 private:
  TlsIdentity identity_;
};

absl::StatusOr<std::unique_ptr<TlsIdentityProvider>> CreateFromFiles(
    std::string key_path, std::string cert_path) {
  auto key_der = LoadPrivateKeyFromFile(key_path.c_str());
  if (!key_der.ok()) {
    return key_der.status();
  }

  auto cert_der = LoadCertificateFromFile(cert_path.c_str());
  if (!cert_der.ok()) {
    return cert_der.status();
  }

  return std::make_unique<StaticCertIdentityProvider>(TlsIdentity{
      .key_asn1 = std::move(*key_der), .cert_asn1 = std::move(*cert_der)});
}

absl::StatusOr<std::unique_ptr<TlsIdentityProvider>> CreateSelfSigned() {
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!pkey) {
    return absl::InternalError("Failed to create EVP_PKEY");
  }
  bssl::UniquePtr<EC_KEY> ec_key(
      EC_KEY_new_by_curve_name(NID_X9_62_prime256v1));
  if (!ec_key) {
    return absl::InternalError("Failed to create EC_KEY");
  }
  if (!EC_KEY_generate_key(ec_key.get())) {
    return absl::InternalError("Failed to generate EC key");
  }
  if (!EVP_PKEY_assign_EC_KEY(pkey.get(), ec_key.release())) {
    return absl::InternalError("Failed to assign EC key to PKEY");
  }

  bssl::UniquePtr<X509> x509(X509_new());
  if (!x509) {
    return absl::InternalError("Failed to allocate X509");
  }

  X509_set_version(x509.get(), 2);
  ASN1_INTEGER_set(X509_get_serialNumber(x509.get()), 1);
  X509_gmtime_adj(X509_get_notBefore(x509.get()), 0);
  X509_gmtime_adj(X509_get_notAfter(x509.get()), 31536000L);  // 1 year expiry
  X509_set_pubkey(x509.get(), pkey.get());

  X509_NAME* name = X509_get_subject_name(x509.get());
  X509_NAME_add_entry_by_txt(
      name, "CN", MBSTRING_ASC,
      reinterpret_cast<const unsigned char*>("oak-session-tls"), -1, -1, 0);
  X509_set_issuer_name(x509.get(), name);

  if (!X509_sign(x509.get(), pkey.get(), EVP_sha256())) {
    return absl::InternalError("Failed to sign certificate");
  }

  int key_len = i2d_PrivateKey(pkey.get(), nullptr);
  if (key_len < 0) {
    return absl::InternalError("Failed to get DER length for private key");
  }
  std::string key_der;
  key_der.resize(key_len);
  unsigned char* p1 = reinterpret_cast<unsigned char*>(key_der.data());
  if (i2d_PrivateKey(pkey.get(), &p1) < 0) {
    return absl::InternalError("Failed to convert private key to DER");
  }

  int cert_len = i2d_X509(x509.get(), nullptr);
  if (cert_len < 0) {
    return absl::InternalError("Failed to get DER length for certificate");
  }
  std::string cert_der;
  cert_der.resize(cert_len);
  unsigned char* p2 = reinterpret_cast<unsigned char*>(cert_der.data());
  if (i2d_X509(x509.get(), &p2) < 0) {
    return absl::InternalError("Failed to convert certificate to DER");
  }

  return std::make_unique<StaticCertIdentityProvider>(TlsIdentity{
      .key_asn1 = std::move(key_der), .cert_asn1 = std::move(cert_der)});
}

}  // namespace oak::session::tls::util
