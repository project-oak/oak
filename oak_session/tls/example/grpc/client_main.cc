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
#include "grpcpp/grpcpp.h"
#include "oak_session/tls/example/grpc/service.grpc.pb.h"
#include "oak_session/tls/oak_session_tls.h"
#include "oak_session/tls/util.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/ssl.h"

ABSL_FLAG(std::string, port, "8080", "Port for the server to listen on");
ABSL_FLAG(std::string, ca_cert, "oak_session/tls/testing/test_ca.pem",
          "Path to the CA certificate (trust anchor for server verification)");
ABSL_FLAG(std::string, client_key, "oak_session/tls/testing/test_client.key",
          "Path to the client key (for mTLS)");
ABSL_FLAG(std::string, client_cert, "oak_session/tls/testing/test_client.pem",
          "Path to the client certificate (for mTLS)");

using oak::session::tls::example::TlsOverGrpc;
using oak::session::tls::example::TlsSessionRequest;
using oak::session::tls::example::TlsSessionResponse;

namespace oak::session::tls::example {
void RunClient() {
  std::string server_address =
      absl::StrCat("localhost:", absl::GetFlag(FLAGS_port));
  auto channel =
      grpc::CreateChannel(server_address, grpc::InsecureChannelCredentials());
  auto stub = TlsOverGrpc::NewStub(channel);

  absl::StatusOr<std::string> client_key_asn1 =
      util::LoadPrivateKeyFromFile(absl::GetFlag(FLAGS_client_key).c_str());
  absl::StatusOr<std::string> client_cert_asn1 =
      util::LoadCertificateFromFile(absl::GetFlag(FLAGS_client_cert).c_str());

  class StaticIdentityProvider : public TlsIdentityProvider {
   public:
    StaticIdentityProvider(std::string key, std::string cert)
        : current_identity_{.key_asn1 = std::move(key),
                            .cert_asn1 = std::move(cert)} {}
    absl::StatusOr<TlsIdentity> GetIdentity() override {
      return current_identity_;
    }

   private:
    TlsIdentity current_identity_;
  };

  auto trust_anchor =
      util::CreateTrustAnchorFromFile(absl::GetFlag(FLAGS_ca_cert));
  if (!trust_anchor.ok()) {
    LOG(FATAL) << "Failed to load trust anchor: " << trust_anchor.status();
  }

  absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> tls_context =
      OakSessionTlsContext::Create(ClientContextConfig{
          .server_trust_anchor_provider = std::move(*trust_anchor),
          .tls_identity_provider = std::make_unique<StaticIdentityProvider>(
              *client_key_asn1, *client_cert_asn1),
      });
  grpc::ClientContext grpc_context;
  auto stream = stub->TlsSession(&grpc_context);

  // Use NewInitializedSession with blocking send/receive callbacks.
  absl::StatusOr<InitializedSession> initialized_session =
      (*tls_context)
          ->NewInitializedSession(
              /*send=*/
              [&](absl::string_view data) {
                TlsSessionRequest request;
                request.set_frame(std::string(data));
                if (!stream->Write(request)) {
                  return absl::InternalError("Failed to write to stream");
                }
                return absl::OkStatus();
              },
              /*receive=*/
              [&]() -> absl::StatusOr<std::string> {
                TlsSessionResponse response;
                if (!stream->Read(&response)) {
                  return absl::InternalError(
                      "Stream closed unexpectedly during handshake");
                }
                return response.frame();
              });
  if (!initialized_session.ok()) {
    LOG(FATAL) << "Failed to initialize TLS session: "
               << initialized_session.status();
  }
  LOG(INFO) << "Client handshake complete.";
  std::unique_ptr<OakSessionTls>& session = initialized_session->session;

  // Send a message to the server.
  std::string message = "world";

  absl::StatusOr<std::string> encrypted_message = session->Encrypt(message);
  TlsSessionRequest request;
  request.set_frame(*encrypted_message);
  stream->Write(request);

  // Read the response from the server.
  std::string decrypted_message;
  // Loop until we receive non-empty application data. session->Decrypt may
  // return empty data if it processed a post-handshake TLS control frame
  // (e.g., a session ticket).
  while (decrypted_message.empty()) {
    TlsSessionResponse response;
    if (!stream->Read(&response)) {
      LOG(FATAL) << "Stream closed unexpectedly while waiting for response";
    }

    absl::StatusOr<std::string> status_or_decrypted =
        session->Decrypt(response.frame());
    if (!status_or_decrypted.ok()) {
      LOG(FATAL) << "Failed to decrypt message: "
                 << status_or_decrypted.status();
    }
    decrypted_message = *status_or_decrypted;
  }
  LOG(INFO) << "Received: " << decrypted_message;

  LOG(INFO) << "Completing session...";

  stream->WritesDone();
  grpc::Status status = stream->Finish();
  if (!status.ok()) {
    LOG(ERROR) << "RPC failed: " << status.error_message();
  }
}

}  // namespace oak::session::tls::example
int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  oak::session::tls::example::RunClient();
  return 0;
}
