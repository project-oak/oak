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
#ifndef DEV_OAK_MANAGER_H
#define DEV_OAK_MANAGER_H

#include <string>

#include "absl/strings/string_view.h"
#include "asylo/util/logging.h"
#include "oak/proto/enclave.pb.h"
#include "oak/proto/manager.grpc.pb.h"
#include "oak/server/oak_runtime.h"

namespace oak {

class DevOakManager final : public Manager::Service {
 public:
  DevOakManager();

  grpc::Status CreateApplication(grpc::ServerContext* context,
                                 const CreateApplicationRequest* request,
                                 CreateApplicationResponse* response) override;

 private:
  std::string NewApplicationId();
  void InitializeAssertionAuthorities();

  uint64_t application_id_;
  std::unique_ptr<OakRuntime> runtime_;
};

}  // namespace oak
#endif  // DEV_OAK_MANAGER_H