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

#include "cc/containers/sdk/orchestrator_crypto_client.h"

#include <memory>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/common.h"
#include "grpcpp/client_context.h"
#include "grpcpp/support/status.h"
#include "proto/containers/orchestrator_crypto.grpc.pb.h"
#include "proto/containers/orchestrator_crypto.pb.h"

namespace oak::containers::sdk {

namespace {
using grpc::ClientContext;
using ::oak::containers::v1::DeriveSessionKeysRequest;
using ::oak::containers::v1::DeriveSessionKeysResponse;
using ::oak::containers::v1::KeyOrigin;
using ::oak::containers::v1::SignRequest;
using ::oak::containers::v1::SignResponse;
using ::oak::crypto::v1::SessionKeys;
using ::oak::crypto::v1::Signature;
}  // namespace

absl::StatusOr<SessionKeys> OrchestratorCryptoClient::DeriveSessionKeys(
    KeyOrigin key_origin,
    absl::string_view serialized_encapsulated_public_key) const {
  ClientContext context;
  context.set_authority(kContextAuthority);
  DeriveSessionKeysRequest request;
  request.set_key_origin(key_origin);
  request.set_serialized_encapsulated_public_key(
      serialized_encapsulated_public_key);
  DeriveSessionKeysResponse response;

  grpc::Status status = stub_->DeriveSessionKeys(&context, request, &response);
  if (!status.ok()) {
    return absl::InternalError(
        absl::StrCat("couldn't derive session keys: code=", status.error_code(),
                     ", message=", status.error_message()));
  }

  return response.session_keys();
}

absl::StatusOr<Signature> OrchestratorCryptoClient::Sign(
    KeyOrigin key_origin, absl::string_view message) const {
  ClientContext context;
  context.set_authority(kContextAuthority);
  SignRequest request;
  request.set_key_origin(key_origin);
  request.set_message(message);
  SignResponse response;

  grpc::Status status = stub_->Sign(&context, request, &response);
  if (!status.ok()) {
    return absl::InternalError(
        absl::StrCat("couldn't sign message: code=", status.error_code(),
                     ", message=", status.error_message()));
  }

  return response.signature();
}

}  // namespace oak::containers::sdk
