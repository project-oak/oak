/*
 * Copyright 2018 The Project Oak Authors
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

#include "asylo_oak_manager_service.h"

#include "absl/memory/memory.h"
#include "asylo/identity/descriptions.h"
#include "asylo/identity/enclave_assertion_authority_config.pb.h"
#include "asylo/util/logging.h"
#include "asylo/util/statusor.h"

namespace oak {

AsyloOakManagerService::AsyloOakManagerService(absl::string_view enclave_path)
    : Service(), manager_(enclave_path) {}

grpc::Status AsyloOakManagerService::CreateApplication(grpc::ServerContext* context,
                                                       const oak::CreateApplicationRequest* request,
                                                       oak::CreateApplicationResponse* response) {
  asylo::StatusOr<oak::CreateApplicationResponse> result =
      manager_.CreateApplication(request->application_configuration());
  if (!result.ok()) {
    return result.status().ToOtherStatus<grpc::Status>();
  }
  *response = std::move(result.ValueOrDie());
  return grpc::Status::OK;
}

grpc::Status AsyloOakManagerService::TerminateApplication(
    grpc::ServerContext* context, const oak::TerminateApplicationRequest* request,
    oak::TerminateApplicationResponse* response) {
  manager_.TerminateApplication(request->application_id());
  return grpc::Status::OK;
}

}  // namespace oak
