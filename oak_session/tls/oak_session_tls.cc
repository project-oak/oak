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

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::CreateServerContext(absl::string_view server_key_path,
                                          absl::string_view server_cert_path) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_server_method()));
  std::string server_key_path_str(server_key_path);
  std::string server_cert_path_str(server_cert_path);
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  if (SSL_CTX_use_PrivateKey_file(ctx.get(), server_key_path_str.c_str(),
                                  SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load private key");
  }

  if (SSL_CTX_use_certificate_file(ctx.get(), server_cert_path_str.c_str(),
                                   SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load certificate");
  }

  return std::make_unique<OakSessionTlsContext>(OakSessionTlsMode::kServer,
                                                std::move(ctx));
}

absl::StatusOr<std::unique_ptr<OakSessionTlsContext>>
OakSessionTlsContext::CreateClientContext(absl::string_view server_cert_path) {
  std::string server_cert_path_str(server_cert_path);
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_client_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  if (SSL_CTX_load_verify_locations(ctx.get(), server_cert_path_str.c_str(),
                                    nullptr) != 1) {
    return absl::InternalError("Failed to load server certificate");
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
    // Empty SSL_read to update internal state for pending.
    char buf[kReadBufferSize];
    int read_result = SSL_read(ssl_.get(), buf, sizeof(buf));
    if (read_result < 0) {
      int err = SSL_get_error(ssl_.get(), read_result);
      if (err != SSL_ERROR_WANT_READ && err != SSL_ERROR_WANT_WRITE) {
        return absl::InternalError(absl::StrFormat(
            "Failed to read plaintext message from SSL: %d", err));
      }
    } else {
      initial_data_.append(buf, read_result);
    }
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

  char buf[kReadBufferSize];
  int read_result = BIO_read(bio_write_, buf, sizeof(buf));

  if (read_result < 0) {
    return absl::InternalError("Failed to read TLS frame from BIO");
  }

  return std::string(buf, read_result);
}

absl::StatusOr<std::string> OakSessionTls::Decrypt(
    absl::string_view tls_frame) {
  int write_result = BIO_write(bio_read_, tls_frame.data(), tls_frame.size());

  if (write_result <= 0) {
    return absl::InternalError("Failed to write TLS frame to BIO");
  }

  char buf[kReadBufferSize];
  int read_result = SSL_read(ssl_.get(), buf, sizeof(buf));

  if (read_result < 0) {
    int err = SSL_get_error(ssl_.get(), read_result);
    return absl::InternalError(
        absl::StrFormat("Failed to read plaintext message from SSL: %d", err));
  }

  return std::string(buf, read_result);
}

}  // namespace oak::session::tls
