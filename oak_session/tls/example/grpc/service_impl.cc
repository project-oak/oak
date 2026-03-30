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

#include "oak_session/tls/example/grpc/service_impl.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "oak_session/tls/oak_session_tls.h"

namespace oak::session::tls::example {

namespace {
absl::Status SendResponse(
    OakSessionTls* session,
    grpc::ServerReaderWriter<TlsSessionResponse, TlsSessionRequest>* stream,
    const std::string& request_data) {
  std::string response_data = "Hello " + request_data;
  absl::StatusOr<std::string> encrypted_response_data =
      session->Encrypt(response_data);
  TlsSessionResponse response;
  response.set_frame(*encrypted_response_data);
  if (!stream->Write(response)) {
    return absl::InternalError("Failed to write response to stream");
  }
  return absl::OkStatus();
}
}  // namespace

absl::StatusOr<std::unique_ptr<TlsOverGrpcServiceImpl>>
TlsOverGrpcServiceImpl::Create(const std::string& server_key_asn1,
                               const std::string& server_cert_asn1,
                               const std::string& client_cert_path) {
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

  absl::StatusOr<std::unique_ptr<OakSessionTlsContext>> server_ctx =
      OakSessionTlsContext::Create(ServerContextConfig{
          .tls_identity_provider = std::make_unique<StaticIdentityProvider>(
              server_key_asn1, server_cert_asn1),
      });
  if (!server_ctx.ok()) {
    return server_ctx.status();
  }

  return std::unique_ptr<TlsOverGrpcServiceImpl>(
      new TlsOverGrpcServiceImpl(std::move(*server_ctx)));
}

TlsOverGrpcServiceImpl::TlsOverGrpcServiceImpl(
    std::unique_ptr<OakSessionTlsContext> context)
    : context_(std::move(context)) {}

grpc::Status TlsOverGrpcServiceImpl::TlsSession(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<TlsSessionResponse, TlsSessionRequest>* stream) {
  stream->SendInitialMetadata();

  // Use NewInitializedSession with blocking send/receive callbacks.
  absl::StatusOr<InitializedSession> initialized_session =
      context_->NewInitializedSession(
          /*send=*/
          [&](absl::string_view data) {
            TlsSessionResponse response;
            response.set_frame(std::string(data));
            if (!stream->Write(response)) {
              return absl::InternalError("Failed to write to stream");
            }
            return absl::OkStatus();
          },
          /*receive=*/
          [&]() -> absl::StatusOr<std::string> {
            TlsSessionRequest request;
            if (!stream->Read(&request)) {
              return absl::InternalError(
                  "Stream closed unexpectedly during handshake");
            }
            return request.frame();
          });
  if (!initialized_session.ok()) {
    return grpc::Status(grpc::StatusCode::INTERNAL,
                        absl::StrCat("Failed to initialize TLS session: ",
                                     initialized_session.status().message()));
  }

  std::string initial_data = std::move(initialized_session->initial_data);
  std::unique_ptr<OakSessionTls>& session = initialized_session->session;
  LOG(INFO) << "Handshake complete, initial data size: " << initial_data.size();
  // Only respond to initial_data if present (for backward compatibility with
  // manual handshake API that bundles initial data with the handshake).
  if (!initial_data.empty()) {
    absl::Status send_response_status =
        SendResponse(session.get(), stream, initial_data);
    if (!send_response_status.ok()) {
      return grpc::Status(grpc::StatusCode::INTERNAL,
                          "Failed to send initial response");
    }
  }

  TlsSessionRequest request;
  while (stream->Read(&request)) {
    LOG(INFO) << "Got next message...";

    absl::StatusOr<std::string> received = session->Decrypt(request.frame());
    if (!received.ok()) {
      return grpc::Status(grpc::StatusCode::INTERNAL,
                          "Failed to decrypt message");
    }
    absl::Status send_response_status =
        SendResponse(session.get(), stream, *received);
    if (!send_response_status.ok()) {
      return grpc::Status(grpc::StatusCode::INTERNAL,
                          "Failed to send response");
    }
  }

  return grpc::Status::OK;
}

namespace {}

}  // namespace oak::session::tls::example
