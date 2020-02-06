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

#include "oak/server/dev/dev_oak_manager.h"
#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "asylo/util/statusor.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/server/dev/dev_oak_manager.h"

namespace oak {

DevOakManager::DevOakManager() : Service(), loader_() {}

grpc::Status DevOakManager::CreateApplication(grpc::ServerContext*,
                                              const oak::CreateApplicationRequest* request,
                                              oak::CreateApplicationResponse* response) {
  asylo::StatusOr<oak::CreateApplicationResponse> result =
      loader_.CreateApplication(request->application_configuration());
  if (!result.ok()) {
    return result.status().ToOtherStatus<grpc::Status>();
  }
  *response = std::move(result.ValueOrDie());
  return grpc::Status::OK;
}

grpc::Status DevOakManager::TerminateApplication(grpc::ServerContext*,
                                                 const oak::TerminateApplicationRequest* request,
                                                 oak::TerminateApplicationResponse*) {
  return loader_.TerminateApplication(request->application_id());
}

}  // namespace oak
