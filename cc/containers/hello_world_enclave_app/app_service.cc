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
#include "cc/containers/hello_world_enclave_app/app_service.h"

#include <string>

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/oak_session.h"
#include "cc/crypto/common.h"
#include "cc/crypto/server_encryptor.h"
#include "cc/utils/status/status.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers/examples/hello_world/proto/hello_world.grpc.pb.h"
#include "oak_containers/examples/hello_world/proto/hello_world.pb.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/service_streaming.pb.h"

namespace oak::containers::hello_world_enclave_app {

using ::oak::session::ServerSession;
using ::oak::session::v1::PlaintextMessage;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;
using ::oak::session::v1::SessionRequest;
using ::oak::session::v1::SessionResponse;
using ::oak::util::status::Annotate;

grpc::Status FromAbsl(const absl::Status& status) {
  return grpc::Status(static_cast<grpc::StatusCode>(status.code()),
                      std::string(status.message()));
}

std::string EnclaveApplicationImpl::HandleRequest(absl::string_view request) {
  return absl::StrCat("Hello from the enclave, ", request,
                      "! Btw, the app has a config with a length of ",
                      application_config_.size(), " bytes.");
}

grpc::Status EnclaveApplicationImpl::LegacySession(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<ResponseWrapper, RequestWrapper>* stream) {
  absl::Status status = oak_session_context_.OakSession(
      stream, [this](absl::string_view request) -> absl::StatusOr<std::string> {
        return HandleRequest(request);
      });

  return FromAbsl(status);
}

grpc::Status EnclaveApplicationImpl::OakSession(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<SessionResponse, SessionRequest>* stream) {
  absl::StatusOr<std::unique_ptr<ServerSession>> session =
      ServerSession::Create(
          session::SessionConfigBuilder(session::AttestationType::kUnattested,
                                        session::HandshakeType::kNoiseNN)
              .Build());
  if (!session.ok()) {
    return FromAbsl(
        Annotate(session.status(), "Failed to create server session"));
  }

  // Handshake
  SessionRequest request;
  while (!(*session)->IsOpen()) {
    if (!stream->Read(&request)) {
      // Client half-close.
      return FromAbsl(absl::OkStatus());
    }

    absl::Status put_status = (*session)->PutIncomingMessage(request);
    if (!put_status.ok()) {
      return FromAbsl(Annotate(put_status, "Failed to put init message."));
    }

    absl::StatusOr<std::optional<session::v1::SessionResponse>>
        outgoing_message = (*session)->GetOutgoingMessage();
    if (!outgoing_message.ok()) {
      return FromAbsl(Annotate(outgoing_message.status(),
                               "Failed to get next init response."));
    }

    if (*outgoing_message) {
      stream->Write(**outgoing_message);
    }
  }

  // Handshake done, process requests until closed.
  while (true) {
    if (!stream->Read(&request)) {
      // Client half-close.
      grpc::Status();
    }

    absl::Status put_status = (*session)->PutIncomingMessage(request);
    if (!put_status.ok()) {
      return FromAbsl(Annotate(put_status, "Failed to put encrypted message."));
    }

    absl::StatusOr<std::optional<ffi::RustBytes>> request_bytes =
        (*session)->ReadToRustBytes();
    if (!request_bytes.ok()) {
      return FromAbsl(
          Annotate(put_status, "Failed to read next encrypted request."));
    }
    if (!*request_bytes) {
      return FromAbsl(absl::InternalError(
          "Wrote an encrypted message but no data out(library error)"));
    }
    std::string unencrypted_response = HandleRequest(**request_bytes);

    absl::Status write_result = (*session)->Write(unencrypted_response);
    if (!write_result.ok()) {
      return FromAbsl(
          Annotate(write_result, "Failed to read next encrypted request."));
    }

    absl::StatusOr<std::optional<session::v1::SessionResponse>>
        outgoing_response = (*session)->GetOutgoingMessage();
    if (!outgoing_response.ok()) {
      return FromAbsl(
          Annotate(outgoing_response.status(),
                   "Wrote message to encrypt but got no outgoing message "
                   "(library error)."));
    }

    if (!stream->Write(**outgoing_response)) {
      return FromAbsl(absl::InternalError("Failed to write"));
    }
  }

  return grpc::Status();
}

grpc::Status EnclaveApplicationImpl::PlaintextSession(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<PlaintextMessage, PlaintextMessage>* stream) {
  PlaintextMessage request;
  while (stream->Read(&request)) {
    std::string response_text = HandleRequest(request.plaintext());
    PlaintextMessage response;
    *(response.mutable_plaintext()) = response_text;
    stream->Write(response);
  }
  return grpc::Status();
}

}  // namespace oak::containers::hello_world_enclave_app
