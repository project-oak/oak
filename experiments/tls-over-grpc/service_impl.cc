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

#include "experiments/tls-over-grpc/service_impl.h"

#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/log/log.h"
#include "openssl/err.h"

namespace experiments::tls_over_grpc {

namespace {}  // namespace

absl::StatusOr<std::unique_ptr<TlsOverGrpcServiceImpl>>
TlsOverGrpcServiceImpl::Create(const std::string& server_key_path,
                               const std::string& server_cert_path,
                               const std::string& client_cert_path) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_server_method()));
  if (!ctx) {
    return absl::InternalError("Failed to create SSL_CTX");
  }

  if (SSL_CTX_use_PrivateKey_file(ctx.get(), server_key_path.c_str(),
                                  SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load private key");
  }

  if (SSL_CTX_use_certificate_file(ctx.get(), server_cert_path.c_str(),
                                   SSL_FILETYPE_PEM) != 1) {
    return absl::InternalError("Failed to load certificate");
  }

  // mTLS setup
  SSL_CTX_set_verify(
      ctx.get(), SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, nullptr);

  if (SSL_CTX_load_verify_locations(ctx.get(), client_cert_path.c_str(),
                                    nullptr) != 1) {
    LOG(FATAL) << "Failed to load client trust anchor";
  }

  return std::unique_ptr<TlsOverGrpcServiceImpl>(
      new TlsOverGrpcServiceImpl(std::move(ctx)));
}

TlsOverGrpcServiceImpl::TlsOverGrpcServiceImpl(bssl::UniquePtr<SSL_CTX> ctx)
    : ctx_(std::move(ctx)) {}

grpc::Status TlsOverGrpcServiceImpl::TlsSession(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<TlsSessionResponse, TlsSessionRequest>* stream) {
  bssl::UniquePtr<SSL> ssl(SSL_new(ctx_.get()));
  if (!ssl) {
    return grpc::Status(grpc::StatusCode::INTERNAL, "Failed to create SSL");
  }

  // Enable the BIO API for this SSL instance.
  BIO* rbio = BIO_new(BIO_s_mem());
  BIO* wbio = BIO_new(BIO_s_mem());
  SSL_set_bio(ssl.get(), rbio, wbio);

  // Configure this SSL instance to be a server.
  SSL_set_accept_state(ssl.get());

  LOG(INFO) << "Starting message loop...";
  TlsSessionRequest request;
  while (stream->Read(&request)) {
    LOG(INFO) << "Got next message...";

    BIO_write(rbio, request.frame().data(), request.frame().size());

    if (!SSL_is_init_finished(ssl.get())) {
      LOG(INFO) << "Next init step";
      int ret = SSL_do_handshake(ssl.get());
      if (ret < 0) {
        int err = SSL_get_error(ssl.get(), ret);
        if (err != SSL_ERROR_WANT_READ && err != SSL_ERROR_WANT_WRITE) {
          return grpc::Status(grpc::StatusCode::INTERNAL,
                              absl::StrFormat("TLS handshake failed: %d", err));
        }
      }
    }

    // Check again if init is finished, sometimes the first data packet is what
    // triggers handshake completion.
    if (SSL_is_init_finished(ssl.get())) {
      LOG(INFO) << "Data packet";
      char buf[4096];
      int len = SSL_read(ssl.get(), buf, sizeof(buf));
      LOG(INFO) << "Read " << len << " bytes";
      if (len > 0) {
        std::string received(buf, len);
        LOG(INFO) << "Received: " << received;
        std::string prefix("Hello ");
        std::string message = prefix + received;
        SSL_write(ssl.get(), message.data(), message.size());
      } else {
        int err = SSL_get_error(ssl.get(), len);
        if (err != SSL_ERROR_WANT_READ) {
          return grpc::Status(grpc::StatusCode::INTERNAL,
                              absl::StrFormat("TLS read failed: %d", err));
        }
      }
    }

    LOG(INFO) << "Reading response to send...";
    char buf[4096];
    int len = BIO_read(wbio, buf, sizeof(buf));
    LOG(INFO) << "Read " << len << " bytes to send";
    if (len > 0) {
      TlsSessionResponse response;
      response.set_frame(std::string(buf, len));
      stream->Write(response);
    }

    LOG(INFO) << "Await next message...";
  }

  SSL_clear(ssl.get());

  LOG(INFO) << "Read loop finished.";
  return grpc::Status::OK;
}

}  // namespace experiments::tls_over_grpc
