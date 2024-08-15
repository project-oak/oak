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
#include "cc/containers/hello_world_trusted_app/app_service.h"

#include <string>

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "cc/containers/sdk/oak_session.h"
#include "cc/crypto/common.h"
#include "cc/crypto/server_encryptor.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "oak_containers/examples/hello_world/proto/hello_world.grpc.pb.h"
#include "oak_containers/examples/hello_world/proto/hello_world.pb.h"
#include "proto/crypto/crypto.pb.h"
#include "proto/session/service_streaming.pb.h"

namespace oak::oak_containers_hello_world_trusted_app {

using ::oak::session::v1::RequestWrapper;
using ::oak::session::v1::ResponseWrapper;

grpc::Status TrustedApplicationImpl::Session(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<ResponseWrapper, RequestWrapper>* stream) {
  absl::string_view application_config = application_config_;
  absl::Status status = oak_session_context_.OakSession(
      stream,
      [&application_config](
          absl::string_view request) -> absl::StatusOr<std::string> {
        return absl::StrCat(
            "Hello from the trusted side, ", request,
            "! Btw, the Trusted App has a config with a length of ",
            application_config.size(), " bytes.");
      });

  return grpc::Status(static_cast<grpc::StatusCode>(status.code()),
                      std::string(status.message()));
}

}  // namespace oak::oak_containers_hello_world_trusted_app
