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
ABSL_FLAG(std::string, server_cert, "oak_session/tls/testing/server.pem",
          "Path to the server certificate");
ABSL_FLAG(std::string, client_key, "oak_session/tls/testing/client.key",
          "Path to the client key (for mTLS)");
ABSL_FLAG(std::string, client_cert, "oak_session/tls/testing/client.pem",
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

  absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> tls_context =
      OakSessionTlsContext::Create(ClientContextConfig{
          .server_trust_anchor_path = absl::GetFlag(FLAGS_server_cert),
          .tls_identity =
              TlsIdentity{
                  .key_asn1 = *client_key_asn1,
                  .cert_asn1 = *client_cert_asn1,
              },
      });
  grpc::ClientContext grpc_context;
  auto stream = stub->TlsSession(&grpc_context);

  absl::StatusOr<std::unique_ptr<OakSessionTlsInitializer>> initializer =
      (*tls_context)->NewSession();
  if (!initializer.ok()) {
    LOG(FATAL) << "Failed to create TLS initializer: " << initializer.status();
  }

  while (!(*initializer)->IsReady()) {
    LOG(INFO) << "Send next init message";
    absl::StatusOr<std::string> init_message = (*initializer)->GetTLSFrame();
    if (!init_message.ok()) {
      LOG(FATAL) << "Failed to get TLS frame from initializer: "
                 << init_message.status();
    }
    LOG(INFO) << "Read " << init_message->size() << " bytes init message.";
    TlsSessionRequest request;
    request.set_frame(*init_message);
    stream->Write(request);
    LOG(INFO) << "Sent init message";

    TlsSessionResponse response;
    if (stream->Read(&response)) {
      LOG(INFO) << "Got handshake response";
      absl::Status status = (*initializer)->PutTLSFrame(response.frame());
      if (!status.ok()) {
        LOG(FATAL) << "Failed to put TLS frame into initializer: " << status;
      }
    } else {
      LOG(FATAL) << "Stream closed unexpectedly during handshake";
    }
  }

  LOG(INFO) << "Client handshake complete.";
  absl::StatusOr<std::unique_ptr<OakSessionTls>> session =
      (*initializer)->GetOpenSession();
  if (!session.ok()) {
    LOG(FATAL) << "Failed to get open client session: " << session.status();
  }

  // Send a message to the server.
  std::string message = "world";

  absl::StatusOr<std::string> encrypted_message = (*session)->Encrypt(message);
  TlsSessionRequest request;
  request.set_frame(*encrypted_message);
  stream->Write(request);

  // Read the response from the server.
  TlsSessionResponse response;
  if (!stream->Read(&response)) {
    LOG(FATAL) << "Stream closed unexpectedly while waiting for response";
  }

  absl::StatusOr<std::string> decrypted_message =
      (*session)->Decrypt(response.frame());
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
