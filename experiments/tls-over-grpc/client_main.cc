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

#include <iostream>
#include <memory>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "experiments/tls-over-grpc/service.grpc.pb.h"
#include "grpcpp/grpcpp.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/ssl.h"

ABSL_FLAG(std::string, port, "8080", "Port for the server to listen on");
ABSL_FLAG(std::string, server_cert, "experiments/tls-over-grpc/server.pem",
          "Path to the server certificate");
ABSL_FLAG(std::string, client_key, "experiments/tls-over-grpc/client.key",
          "Path to the client key (for mTLS)");
ABSL_FLAG(std::string, client_cert, "experiments/tls-over-grpc/client.pem",
          "Path to the client certificate (for mTLS)");

using experiments::tls_over_grpc::TlsOverGrpc;
using experiments::tls_over_grpc::TlsSessionRequest;
using experiments::tls_over_grpc::TlsSessionResponse;

void RunClient() {
  std::string server_address =
      absl::StrCat("localhost:", absl::GetFlag(FLAGS_port));
  auto channel =
      grpc::CreateChannel(server_address, grpc::InsecureChannelCredentials());
  auto stub = TlsOverGrpc::NewStub(channel);

  grpc::ClientContext context;
  auto stream = stub->TlsSession(&context);

  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_client_method()));
  if (!ctx) {
    LOG(FATAL) << "Failed to create SSL_CTX";
  }

  if (SSL_CTX_use_certificate_file(ctx.get(),
                                   absl::GetFlag(FLAGS_client_cert).c_str(),
                                   SSL_FILETYPE_PEM) != 1) {
    LOG(FATAL) << "Failed to load client certificate";
  }

  if (SSL_CTX_use_PrivateKey_file(ctx.get(),
                                  absl::GetFlag(FLAGS_client_key).c_str(),
                                  SSL_FILETYPE_PEM) != 1) {
    LOG(FATAL) << "Failed to load client private key";
  }

  if (SSL_CTX_load_verify_locations(
          ctx.get(), absl::GetFlag(FLAGS_server_cert).c_str(), nullptr) != 1) {
    LOG(FATAL) << "Failed to load server trust anchor";
  }

  bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
  if (!ssl) {
    LOG(FATAL) << "Failed to create SSL";
  }

  // Enable the BIO API for this SSL instance.
  BIO* rbio(BIO_new(BIO_s_mem()));
  BIO* wbio(BIO_new(BIO_s_mem()));
  SSL_set_bio(ssl.get(), rbio, wbio);

  // Configure this SSL instance to be a client.
  SSL_set_connect_state(ssl.get());

  // Initiate the handshake.
  int ret = SSL_do_handshake(ssl.get());
  if (ret < 0) {
    int err = SSL_get_error(ssl.get(), ret);
    if (err != SSL_ERROR_WANT_READ) {
      LOG(FATAL) << "TLS handshake init failed: " << err << std::endl;
    }
  }

  while (!SSL_is_init_finished(ssl.get())) {
    LOG(INFO) << "Send next init message";
    char buf[4096];
    int len = BIO_read(wbio, buf, sizeof(buf));
    LOG(INFO) << "Read " << len << " bytes init message.";
    if (len > 0) {
      TlsSessionRequest request;
      request.set_frame(std::string(buf, len));
      stream->Write(request);
      LOG(INFO) << "Sent init message";
    }

    TlsSessionResponse response;
    if (stream->Read(&response)) {
      LOG(INFO) << "Got handshake response";
      BIO_write(rbio, response.frame().data(), response.frame().size());
      int ret = SSL_do_handshake(ssl.get());
      if (ret < 0) {
        int err = SSL_get_error(ssl.get(), ret);
        if (err != SSL_ERROR_WANT_READ && err != SSL_ERROR_WANT_WRITE) {
          LOG(FATAL) << "TLS handshake failed: " << err << std::endl;
        }
      }
    } else {
      break;
    }
  }

  LOG(INFO) << "TLS handshake complete";

  // Send a message to the server.
  std::string message = "world";
  SSL_write(ssl.get(), message.data(), message.size());

  char buf[4096];
  int len = BIO_read(wbio, buf, sizeof(buf));
  if (len > 0) {
    LOG(INFO) << "Sending data message of size " << len;
    TlsSessionRequest request;
    request.set_frame(std::string(buf, len));
    stream->Write(request);
  }

  // Read the response from the server.
  TlsSessionResponse response;
  if (stream->Read(&response)) {
    BIO_write(rbio, response.frame().data(), response.frame().size());
    len = SSL_read(ssl.get(), buf, sizeof(buf));
    if (len > 0) {
      std::string received(buf, len);
      LOG(INFO) << "Received: " << received;
    }
  }

  LOG(INFO) << "Completing session...";

  stream->WritesDone();
  grpc::Status status = stream->Finish();
  if (!status.ok()) {
    LOG(ERROR) << "RPC failed: " << status.error_message();
  }
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  RunClient();
  return 0;
}
