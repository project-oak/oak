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

#include "cc/containers/sdk/oak_session.h"

#include <string>

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/common.h"
#include "cc/crypto/server_encryptor.h"
#include "grpcpp/impl/proto_utils.h"
#include "grpcpp/support/sync_stream.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/service_streaming.pb.h"

using ::oak::crypto::DecryptionResult;
using ::oak::crypto::ServerEncryptor;
using ::oak::crypto::v1::EncryptedResponse;
using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;

constexpr absl::string_view kEmptyAssociatedData = "";

namespace oak::containers::sdk {

absl::Status OakSessionContext::OakSession(
    ::grpc::ServerReaderWriter<ResponseWrapper, RequestWrapper>* stream,
    absl::AnyInvocable<absl::StatusOr<std::string>(absl::string_view)>
        handle_request) {
  stream->SendInitialMetadata();

  RequestWrapper request;

  while (stream->Read(&request)) {
    ResponseWrapper response;

    switch (request.request_case()) {
      case RequestWrapper::RequestCase::kGetEndorsedEvidenceRequest: {
        *(response.mutable_get_endorsed_evidence_response()
              ->mutable_endorsed_evidence()) = endorsed_evidence_;
        stream->Write(response);
        break;
      }

      case RequestWrapper::RequestCase::kInvokeRequest: {
        ServerEncryptor server_encryptor(*encryption_key_handle_);

        absl::StatusOr<DecryptionResult> decrypted_request =
            server_encryptor.Decrypt(
                request.invoke_request().encrypted_request());
        if (!decrypted_request.ok()) {
          return decrypted_request.status();
        }

        auto unencrypted_response =
            handle_request(decrypted_request->plaintext);
        if (!unencrypted_response.ok()) {
          return unencrypted_response.status();
        }

        absl::StatusOr<EncryptedResponse> encrypted_response =
            server_encryptor.Encrypt(*unencrypted_response,
                                     kEmptyAssociatedData);
        if (!encrypted_response.ok()) {
          return encrypted_response.status();
        }

        *(response.mutable_invoke_response()->mutable_encrypted_response()) =
            *encrypted_response;
        stream->Write(response);

        break;
      }
      default:
        return absl::InvalidArgumentError("unknown request type");
    }
  }
  return absl::OkStatus();
}

}  // namespace oak::containers::sdk
