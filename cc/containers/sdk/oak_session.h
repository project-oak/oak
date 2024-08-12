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

#ifndef CC_CONTAINERS_SDK_OAK_SESSION_H_
#define CC_CONTAINERS_SDK_OAK_SESSION_H_

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/crypto/encryption_key.h"
#include "grpcpp/support/sync_stream.h"
#include "proto/session/service_streaming.pb.h"

namespace oak::containers::sdk {

// A structure containing the items needed to properly process an Oak Streaming
// Transport message stream.
class OakSessionContext {
 public:
  OakSessionContext(
      oak::session::v1::EndorsedEvidence endorsed_evidence,
      std::unique_ptr<oak::crypto::EncryptionKeyHandle> encryption_key_handle)
      : endorsed_evidence_(std::move(endorsed_evidence)),
        encryption_key_handle_(std::move(encryption_key_handle)) {}

  // A handler for processing a stream of Oak protocol messages inside of a
  // TEE's trusted application handler.
  absl::Status OakSession(
      grpc::ServerReaderWriter<oak::session::v1::ResponseWrapper,
                               oak::session::v1::RequestWrapper>* stream,
      absl::AnyInvocable<absl::StatusOr<std::string>(absl::string_view)>
          handle_request);

 private:
  oak::session::v1::EndorsedEvidence endorsed_evidence_;
  std::unique_ptr<oak::crypto::EncryptionKeyHandle> encryption_key_handle_;
};

}  // namespace oak::containers::sdk

#endif  // THIRD_PARTY_OAK_CC_CONTAINERS_OAK_SESSION_H_
