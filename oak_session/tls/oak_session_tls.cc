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

#include "absl/status/status.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/err.h"
#include "openssl/ssl.h"

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
absl::Status SetTlsIdentity(SSL_CTX* ctx, const TlsIdentity& tls_identity);
}  // namespace

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::Create(const ServerContextConfig& config) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_server_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  absl::Status creds_status = SetTlsIdentity(ctx.get(), config.tls_identity);
  if (!creds_status.ok()) {
    return creds_status;
  }

  if (config.client_trust_anchor_path.has_value()) {
    SSL_CTX_set_verify(
        ctx.get(), SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, nullptr);

    if (SSL_CTX_load_verify_locations(ctx.get(),
                                      config.client_trust_anchor_path->c_str(),
                                      nullptr) != 1) {
      return absl::InternalError("Failed to load trust anchor for client");
    }
  }

  return std::make_unique<OakSessionTlsContext>(OakSessionTlsMode::kServer,
                                                std::move(ctx));
}

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::Create(const ClientContextConfig& config) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_client_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  SSL_CTX_load_verify_locations(
      ctx.get(), config.server_trust_anchor_path.c_str(), nullptr);

  if (config.tls_identity.has_value()) {
    absl::Status creds_status = SetTlsIdentity(ctx.get(), *config.tls_identity);
    if (!creds_status.ok()) {
      return creds_status;
    }
  }

  return std::make_unique<OakSessionTlsContext>(OakSessionTlsMode::kClient,
                                                std::move(ctx));
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsContext::NewSession() {
  switch (mode_) {
    case OakSessionTlsMode::kClient:
      return OakSessionTlsInitializer::CreateClient(ssl_ctx_.get());
    case OakSessionTlsMode::kServer:
      return OakSessionTlsInitializer::CreateServer(ssl_ctx_.get());
  }
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsInitializer::Create(SSL_CTX* ssl_ctx) {
  auto ssl = bssl::UniquePtr<SSL>(SSL_new(ssl_ctx));
  if (!ssl) {
    // TODO: b/448338977 - can we get more error details?
    return absl::FailedPreconditionError("Failed to create SSL instance");
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

  return absl::WrapUnique(
      new OakSessionTlsInitializer(std::move(ssl), rbio, wbio));
}

absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>>
OakSessionTlsInitializer::CreateClient(SSL_CTX* ssl_ctx) {
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> initializer =
      OakSessionTlsInitializer::Create(ssl_ctx);
  if (!initializer.ok()) {
    return initializer.status();
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
OakSessionTlsInitializer::CreateServer(SSL_CTX* ssl_ctx) {
  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> initializer =
      OakSessionTlsInitializer::Create(ssl_ctx);
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

  int write_result = BIO_write(bio_read_, tlsFrame.data(), tlsFrame.size());

  if (write_result <= 0) {
    return absl::InternalError("Failed to write TLS frame to BIO");
  }

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
  char buf[kReadBufferSize];
  int read_result = BIO_read(bio_write_, buf, sizeof(buf));

  if (read_result < 0) {
    return absl::InternalError("Failed to read TLS frame from BIO");
  }

  return std::string(buf, read_result);
}

bool OakSessionTlsInitializer::IsReady() {
  return SSL_is_init_finished(ssl_.get());
}

absl::StatusOr<std::unique_ptr<OakSessionTls>>
OakSessionTlsInitializer::GetOpenClientSession() {
  if (ssl_ == nullptr) {
    return absl::FailedPreconditionError("Initializer is no longer valid.");
  }
  if (!SSL_is_init_finished(ssl_.get())) {
    return absl::FailedPreconditionError("Handshake is not complete yet.");
  }

  auto session = absl::WrapUnique(
      new OakSessionTls(std::move(ssl_), bio_read_, bio_write_));

  bio_read_ = nullptr;
  bio_write_ = nullptr;

  return session;
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

absl::Status SetTlsIdentity(SSL_CTX* ctx, const TlsIdentity& tls_identity) {
  if (SSL_CTX_use_RSAPrivateKey_ASN1(
          ctx, reinterpret_cast<const uint8_t*>(tls_identity.key_asn1.data()),
          tls_identity.key_asn1.size()) != 1) {
    return absl::InternalError("Failed to load private key");
  }

  if (SSL_CTX_use_certificate_ASN1(ctx, tls_identity.cert_asn1.size(),
                                   reinterpret_cast<const uint8_t*>(
                                       tls_identity.cert_asn1.data())) != 1) {
    return absl::InternalError("Failed to load certificate");
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace oak::session::tls
