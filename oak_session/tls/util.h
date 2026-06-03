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
#ifndef OAK_SESSION_TLS_SSL_UTIL_H_
#define OAK_SESSION_TLS_SSL_UTIL_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "oak_session/tls/oak_session_tls.h"

namespace oak::session::tls::util {

absl::StatusOr<std::string> LoadPrivateKeyFromFile(const char* key_path);
absl::StatusOr<std::string> LoadCertificateFromFile(const char* cert_path);
absl::StatusOr<std::vector<std::string>> LoadCertificateChainFromFile(const char* cert_path);

/// An X.509v3 extension to embed in a self-signed certificate.
///
/// Extensions are identified by an OID and contain a DER-encoded value.
/// Use this with `CreateSelfSigned` to embed application-specific data
/// (e.g., attestation evidence) in the certificate.
struct X509Extension {
  /// The OID identifying this extension, in dotted-decimal notation
  /// (e.g., "1.2.3.4.5").
  std::string oid;
  /// The DER-encoded value for this extension.
  std::string value;
  /// Whether this extension is critical. Critical extensions cause
  /// certificate rejection if not understood by the verifier.
  bool critical = false;
};

absl::StatusOr<std::unique_ptr<TlsIdentityProvider>> CreateFromFiles(
    std::string key_path, std::string cert_path);

/// Creates a self-signed TlsIdentityProvider with optional X.509 extensions.
///
/// The `server_name` parameter sets both the Common Name (CN) and the Subject
/// Alternative Name (SAN) DNS entry in the generated certificate. It defaults
/// to `kDefaultServerName` ("oak-session-tls").
///
/// The SAN must match the client's `expected_server_name` for certificate
/// verification to succeed.
absl::StatusOr<std::unique_ptr<TlsIdentityProvider>> CreateSelfSigned(
    absl::Span<const X509Extension> extensions = {},
    absl::string_view server_name = kDefaultServerName);

/// Creates a TrustAnchorProvider that loads a PEM certificate from a file path.
/// The file is read each time GetTrustAnchor() is called.
absl::StatusOr<std::unique_ptr<TrustAnchorProvider>> CreateTrustAnchorFromFile(
    std::string cert_path);

/// Creates a TrustAnchorProvider that always returns the provided DER-encoded
/// certificate.
std::unique_ptr<TrustAnchorProvider> CreateStaticTrustAnchor(std::string cert_der);

}  // namespace oak::session::tls::util

#endif  // OAK_SESSION_TLS_SSL_UTIL_H__
