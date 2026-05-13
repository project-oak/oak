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

#include "oak_session/tls/oak_session_tls.h"

#include "absl/base/call_once.h"
#include "absl/status/status.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/err.h"
#include "openssl/evp.h"
#include "openssl/ssl.h"
#include "openssl/x509.h"

constexpr int kMaxTlsFrameSize = 16 * 1024;  // 16 KB

// For now, we hard-code read buffers to be the maximum TLS frame size.
// This makes the BIO read/write logic easier, as we don't need to loop to
// ensure we've read all pending data.
// TODO: b/448338977 - improve testing for various data sizes and ensure that
// read/write paths are robust.
constexpr int kReadBufferSize = kMaxTlsFrameSize;

namespace oak::session::tls {

namespace {
absl::StatusOr<std::string> BioReadAll(BIO* bio);
absl::StatusOr<std::string> SslReadAll(SSL* ssl);
absl::Status SetTlsIdentity(SSL* ssl, const TlsIdentity& tls_identity);

static int g_custom_verifier_ex_index = -1;
static absl::once_flag g_custom_verifier_ex_index_once;

int GetCustomVerifierExIndex() {
  absl::call_once(g_custom_verifier_ex_index_once, []() {
    g_custom_verifier_ex_index =
        SSL_get_ex_new_index(0, nullptr, nullptr, nullptr, nullptr);
  });
  return g_custom_verifier_ex_index;
}

int VerifyCallback(X509_STORE_CTX* ctx, void* arg) {
  int ok = X509_verify_cert(ctx);

  SSL* ssl = static_cast<SSL*>(
      X509_STORE_CTX_get_ex_data(ctx, SSL_get_ex_data_X509_STORE_CTX_idx()));
  if (!ssl) return ok;

  CustomCertVerifier* verifier = static_cast<CustomCertVerifier*>(
      SSL_get_ex_data(ssl, GetCustomVerifierExIndex()));
  if (!verifier) return ok;

  int err = X509_STORE_CTX_get_error(ctx);

  STACK_OF(X509)* chain = X509_STORE_CTX_get0_chain(ctx);
  if (!chain) return ok;

  std::vector<std::string> cert_chain;
  for (size_t i = 0; i < sk_X509_num(chain); ++i) {
    X509* cert = sk_X509_value(chain, i);
    unsigned char* der = nullptr;
    int len = i2d_X509(cert, &der);
    if (len >= 0) {
      cert_chain.push_back(std::string(reinterpret_cast<char*>(der), len));
      OPENSSL_free(der);
    }
  }

  // Execute custom validation
  absl::Status status = (*verifier)(cert_chain, err);
  if (!status.ok()) {
    if (ok > 0) {
      X509_STORE_CTX_set_error(ctx, X509_V_ERR_APPLICATION_VERIFICATION);
    }
    return 0;
  }

  return 1;
}

}  // namespace

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::Create(ServerContextConfig config) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_server_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  SSL_CTX_set_min_proto_version(ctx.get(), TLS1_3_VERSION);

  // Enable PQC support with X25519MLKEM768 as preferred, fallback to X25519.
  // This provides hybrid post-quantum security using ML-KEM-768 combined with
  // classical X25519 key exchange.
  static const uint16_t kGroups[] = {SSL_GROUP_X25519_MLKEM768,
                                     SSL_GROUP_X25519};
  SSL_CTX_set1_group_ids(ctx.get(), kGroups, std::size(kGroups));

  if (config.client_trust_anchor_provider != nullptr ||
      config.custom_cert_verifier.has_value()) {
    SSL_CTX_set_verify(
        ctx.get(), SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, nullptr);

    if (config.custom_cert_verifier.has_value()) {
      SSL_CTX_set_cert_verify_callback(ctx.get(), VerifyCallback, nullptr);
    }
  }

  return std::make_unique<OakSessionTlsContext>(
      OakSessionTlsMode::kServer, std::move(ctx),
      std::move(config.tls_identity_provider),
      std::move(config.client_trust_anchor_provider),
      std::move(config.custom_cert_verifier), "");
}

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::Create(ClientContextConfig config) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_client_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  SSL_CTX_set_min_proto_version(ctx.get(), TLS1_3_VERSION);

  // Enable PQC support with X25519MLKEM768 as preferred, fallback to X25519.
  // This provides hybrid post-quantum security using ML-KEM-768 combined with
  // classical X25519 key exchange.
  static const uint16_t kGroups[] = {SSL_GROUP_X25519_MLKEM768,
                                     SSL_GROUP_X25519};
  SSL_CTX_set1_group_ids(ctx.get(), kGroups, std::size(kGroups));

  // Unconditionally enable server certificate verification.
  // To bypass verification, the caller must provide a custom verifier.
  SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);

  if (config.custom_cert_verifier.has_value()) {
    SSL_CTX_set_cert_verify_callback(ctx.get(), VerifyCallback, nullptr);
  }

  std::string expected_server_name =
      config.expected_server_name.value_or(std::string(kDefaultServerName));

  return std::make_unique<OakSessionTlsContext>(
      OakSessionTlsMode::kClient, std::move(ctx),
      std::move(config.tls_identity_provider),
      std::move(config.server_trust_anchor_provider),
      std::move(config.custom_cert_verifier), std::move(expected_server_name));
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsContext::NewSession() {
  const TlsIdentity* identity_ptr = nullptr;
  std::optional<TlsIdentity> identity;
  if (tls_identity_provider_ != nullptr) {
    auto identity_or = tls_identity_provider_->GetIdentity();
    if (!identity_or.ok()) {
      return identity_or.status();
    }
    identity = std::move(*identity_or);
    identity_ptr = &*identity;
  }

  std::optional<std::string> trust_anchor;
  const std::string* trust_anchor_ptr = nullptr;
  if (trust_anchor_provider_ != nullptr) {
    auto anchor_or = trust_anchor_provider_->GetTrustAnchor();
    if (!anchor_or.ok()) {
      return anchor_or.status();
    }
    trust_anchor = std::move(*anchor_or);
    trust_anchor_ptr = &*trust_anchor;
  }

  switch (mode_) {
    case OakSessionTlsMode::kClient:
      return OakSessionTlsInitializer::CreateClient(
          ssl_ctx_.get(), expected_server_name_, identity_ptr, trust_anchor_ptr,
          custom_cert_verifier_.has_value() ? &*custom_cert_verifier_
                                            : nullptr);
    case OakSessionTlsMode::kServer:
      return OakSessionTlsInitializer::CreateServer(
          ssl_ctx_.get(), identity_ptr, trust_anchor_ptr,
          custom_cert_verifier_.has_value() ? &*custom_cert_verifier_
                                            : nullptr);
  }
}

absl::StatusOr<InitializedSession> OakSessionTlsContext::NewInitializedSession(
    SendFn send, ReceiveFn receive) {
  auto initializer_or = NewSession();
  if (!initializer_or.ok()) {
    return initializer_or.status();
  }
  auto initializer = std::move(*initializer_or);

  // Client sends initial frame (ClientHello) before entering the loop.
  if (mode_ == OakSessionTlsMode::kClient) {
    auto outgoing = initializer->GetTLSFrame();
    if (!outgoing.ok()) {
      return outgoing.status();
    }
    auto send_status = send(*outgoing);
    if (!send_status.ok()) {
      return send_status;
    }
  }

  // Unified loop: receive, process, send response (if any).
  while (!initializer->IsReady()) {
    auto incoming = receive();
    if (!incoming.ok()) {
      return incoming.status();
    }
    auto put_status = initializer->PutTLSFrame(*incoming);
    if (!put_status.ok()) {
      return put_status;
    }

    // Send any outgoing response frame.
    if (!initializer->IsReady()) {
      auto outgoing = initializer->GetTLSFrame();
      if (!outgoing.ok()) {
        return outgoing.status();
      }
      if (!outgoing->empty()) {
        auto send_status = send(*outgoing);
        if (!send_status.ok()) {
          return send_status;
        }
      }
    }
  }

  // Drain any final outgoing frame (e.g., client's Finished message).
  auto final_frame = initializer->GetTLSFrame();
  if (final_frame.ok() && !final_frame->empty()) {
    auto send_status = send(*final_frame);
    if (!send_status.ok()) {
      return send_status;
    }
  }

  return initializer->GetOpenSession();
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsInitializer::Create(
    SSL_CTX* ssl_ctx, const TlsIdentity* tls_identity,
    const std::string* trust_anchor,
    const CustomCertVerifier* custom_cert_verifier) {
  auto ssl = bssl::UniquePtr<SSL>(SSL_new(ssl_ctx));
  if (!ssl) {
    // TODO: b/448338977 - can we get more error details?
    return absl::FailedPreconditionError("Failed to create SSL instance");
  }

  if (tls_identity != nullptr) {
    absl::Status identity_status = SetTlsIdentity(ssl.get(), *tls_identity);
    if (!identity_status.ok()) {
      return identity_status;
    }
  }

  if (trust_anchor != nullptr) {
    const uint8_t* ptr = reinterpret_cast<const uint8_t*>(trust_anchor->data());
    X509* cert = d2i_X509(nullptr, &ptr, trust_anchor->size());
    if (cert == nullptr) {
      return absl::InternalError("failed to parse trust anchor certificate");
    }
    X509_STORE* store = X509_STORE_new();
    if (store == nullptr) {
      X509_free(cert);
      return absl::InternalError("failed to create certificate store");
    }
    if (X509_STORE_add_cert(store, cert) != 1) {
      X509_free(cert);
      X509_STORE_free(store);
      return absl::InternalError("failed to add certificate to store");
    }
    X509_free(cert);
    SSL_set1_verify_cert_store(ssl.get(), store);
    X509_STORE_free(store);
  }

  // Enable the BIO API for this SSL instance.
  BIO* rbio = BIO_new(BIO_s_mem());
  if (rbio == nullptr) {
    return absl::InternalError("Failed to create read BIO");
  }

  BIO* wbio = BIO_new(BIO_s_mem());
  if (wbio == nullptr) {
    BIO_free(rbio);
    return absl::InternalError("Failed to create write BIO");
  }

  // SSL_set_bio lets the `SSL` object manage the BIO objects, so we only
  // create and pass raw pointers here.
  SSL_set_bio(ssl.get(), rbio, wbio);

  std::optional<CustomCertVerifier> verifier_copy;
  if (custom_cert_verifier) {
    verifier_copy = *custom_cert_verifier;
  }

  auto initializer = absl::WrapUnique(new OakSessionTlsInitializer(
      std::move(ssl), rbio, wbio, std::move(verifier_copy)));

  if (initializer->custom_verifier_.has_value()) {
    SSL_set_ex_data(initializer->ssl_.get(), GetCustomVerifierExIndex(),
                    &*initializer->custom_verifier_);
  }

  return initializer;
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsInitializer::CreateClient(
    SSL_CTX* ssl_ctx, const std::string& expected_server_name,
    const TlsIdentity* tls_identity, const std::string* trust_anchor,
    const CustomCertVerifier* custom_cert_verifier) {
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> initializer =
      OakSessionTlsInitializer::Create(ssl_ctx, tls_identity, trust_anchor,
                                       custom_cert_verifier);
  if (!initializer.ok()) {
    return initializer.status();
  }

  // Set SNI (Server Name Indication) so the server knows which certificate to
  // present.
  if (!SSL_set_tlsext_host_name((*initializer)->ssl_.get(),
                                expected_server_name.c_str())) {
    return absl::InternalError("failed to set SNI hostname");
  }

  // Enable hostname verification against the server certificate's SAN.
  X509_VERIFY_PARAM* param = SSL_get0_param((*initializer)->ssl_.get());
  X509_VERIFY_PARAM_set_hostflags(param, 0);
  if (!X509_VERIFY_PARAM_set1_host(param, expected_server_name.data(),
                                   expected_server_name.size())) {
    return absl::InternalError(
        "failed to set expected hostname for verification");
  }

  // Set this SSL instance into client mode.
  SSL_set_connect_state((*initializer)->ssl_.get());

  // Initiate the handshake.
  int ret = SSL_do_handshake((*initializer)->ssl_.get());
  if (ret < 0) {
    int err = SSL_get_error((*initializer)->ssl_.get(), ret);
    if (err != SSL_ERROR_WANT_READ) {
      return absl::FailedPreconditionError(
          absl::StrFormat("TLS handshake init failed: %d", err));
    }
  }

  return initializer;
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsInitializer::CreateServer(
    SSL_CTX* ssl_ctx, const TlsIdentity* tls_identity,
    const std::string* trust_anchor,
    const CustomCertVerifier* custom_cert_verifier) {
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> initializer =
      OakSessionTlsInitializer::Create(ssl_ctx, tls_identity, trust_anchor,
                                       custom_cert_verifier);
  if (!initializer.ok()) {
    return initializer.status();
  }

  // Set this SSL instance into server mode.
  SSL_set_accept_state((*initializer)->ssl_.get());

  return initializer;
}

absl::Status OakSessionTlsInitializer::PutTLSFrame(absl::string_view tlsFrame) {
  if (SSL_is_init_finished(ssl_.get())) {
    return absl::FailedPreconditionError("Handshake was already completed.");
  }

  // Write incoming TLS data to the read BIO, making it available to SSL.
  int write_result = BIO_write(bio_read_, tlsFrame.data(), tlsFrame.size());

  if (write_result <= 0) {
    return absl::InternalError("Failed to write TLS frame to BIO");
  }

  // Advance the TLS state machine. This may produce outgoing data in
  // bio_write_.

  int ret = SSL_do_handshake(ssl_.get());
  if (ret < 0) {
    int err = SSL_get_error(ssl_.get(), ret);
    // SSL_ERROR_WANT_READ and SSL_ERROR_WANT_WRITE are not fatal errors:
    // these mean that the state machine accepted the frame, and now needs
    // further information from the sender to continue.
    if (err != SSL_ERROR_WANT_READ && err != SSL_ERROR_WANT_WRITE) {
      return absl::FailedPreconditionError(
          absl::StrFormat("TLS handshake failed: %d", err));
    }
  }

  // If the handshake just completed, check for any application data that was
  // bundled with the final handshake message (common in TLS 1.3).
  if (SSL_is_init_finished(ssl_.get())) {
    auto initial_data = SslReadAll(ssl_.get());

    if (!initial_data.ok()) {
      return initial_data.status();
    }
    initial_data_ = std::move(*initial_data);
  }

  return absl::OkStatus();
}

absl::StatusOr<std::string> OakSessionTlsInitializer::GetTLSFrame() {
  // Read any pending outgoing TLS data from the write BIO.
  // This contains TLS handshake messages generated by SSL_do_handshake().
  return BioReadAll(bio_write_);
}

bool OakSessionTlsInitializer::IsReady() {
  return SSL_is_init_finished(ssl_.get());
}

absl::StatusOr<InitializedSession> OakSessionTlsInitializer::GetOpenSession() {
  if (ssl_ == nullptr) {
    return absl::FailedPreconditionError("Initializer is no longer valid.");
  }
  if (!SSL_is_init_finished(ssl_.get())) {
    return absl::FailedPreconditionError("Handshake is not complete yet.");
  }

  // Transfer ownership of SSL and BIO resources to the new OakSessionTls.
  // After this, the initializer is no longer valid.
  auto session = absl::WrapUnique(
      new OakSessionTls(std::move(ssl_), bio_read_, bio_write_));

  bio_read_ = nullptr;
  bio_write_ = nullptr;

  return InitializedSession{
      .session = std::move(session),
      .initial_data = std::move(initial_data_),
  };
}

absl::StatusOr<std::string> OakSessionTls::Encrypt(
    absl::string_view plaintext_message) {
  int write_result =
      SSL_write(ssl_.get(), plaintext_message.data(), plaintext_message.size());

  if (write_result <= 0) {
    int err = SSL_get_error(ssl_.get(), write_result);
    return absl::InternalError(
        absl::StrFormat("Failed to write plaintext message to SSL: %d", err));
  }

  return BioReadAll(bio_write_);
}

absl::StatusOr<std::string> OakSessionTls::Decrypt(
    absl::string_view tls_frame) {
  int write_result = BIO_write(bio_read_, tls_frame.data(), tls_frame.size());

  if (write_result <= 0) {
    return absl::InternalError("Failed to write TLS frame to BIO");
  }

  return SslReadAll(ssl_.get());
}

uint16_t OakSessionTls::GetNegotiatedGroup() const {
  return SSL_get_group_id(ssl_.get());
}

namespace {

absl::StatusOr<std::string> BioReadAll(BIO* bio) {
  std::string result;
  char buf[kReadBufferSize];

  while (BIO_pending(bio) > 0) {
    int read_result = BIO_read(bio, buf, sizeof(buf));

    if (read_result < 0) {
      return absl::InternalError("Failed to read TLS frame from BIO");
    }

    result.append(buf, read_result);
  }

  return result;
}

absl::StatusOr<std::string> SslReadAll(SSL* ssl) {
  std::string result;
  char buf[kReadBufferSize];

  while (true) {
    int read_result = SSL_read(ssl, buf, sizeof(buf));

    if (read_result < 0) {
      int err = SSL_get_error(ssl, read_result);

      if (err == SSL_ERROR_WANT_READ) {
        // No more data available for now.
        break;
      }

      return absl::InternalError(absl::StrFormat(
          "Failed to read plaintext message from SSL: %d", err));
    }

    result.append(buf, read_result);
  };

  return result;
}

absl::Status SetTlsIdentity(SSL* ssl, const TlsIdentity& tls_identity) {
  // Use d2i_AutoPrivateKey to auto-detect the key type (RSA, EC, etc.)
  // rather than assuming RSA.
  const unsigned char* key_data =
      reinterpret_cast<const unsigned char*>(tls_identity.key_asn1.data());
  bssl::UniquePtr<EVP_PKEY> pkey(
      d2i_AutoPrivateKey(nullptr, &key_data, tls_identity.key_asn1.size()));
  if (!pkey) {
    return absl::InternalError("Failed to parse private key");
  }
  if (SSL_use_PrivateKey(ssl, pkey.get()) != 1) {
    return absl::InternalError("Failed to load private key");
  }

  if (tls_identity.cert_chain.empty()) {
    return absl::InvalidArgumentError("certificate chain is empty");
  }

  // Load the leaf certificate (first certificate in the chain)
  const std::string& leaf_cert = tls_identity.cert_chain[0];
  if (SSL_use_certificate_ASN1(
          ssl, reinterpret_cast<const uint8_t*>(leaf_cert.data()),
          leaf_cert.size()) != 1) {
    return absl::InternalError("Failed to load leaf certificate");
  }

  // Load the rest of the certificate chain
  for (size_t i = 1; i < tls_identity.cert_chain.size(); ++i) {
    const std::string& cert_der = tls_identity.cert_chain[i];
    const uint8_t* ptr = reinterpret_cast<const uint8_t*>(cert_der.data());
    bssl::UniquePtr<X509> cert(d2i_X509(nullptr, &ptr, cert_der.size()));
    if (!cert) {
      return absl::InternalError("Failed to parse chain certificate");
    }
    if (SSL_add1_chain_cert(ssl, cert.get()) != 1) {
      return absl::InternalError("Failed to add certificate to chain");
    }
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace oak::session::tls
