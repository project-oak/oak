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

#ifndef OAK_SERVER_DEV_DEV_OAK_LOADER_H_
#define OAK_SERVER_DEV_DEV_OAK_LOADER_H_

#include <string>
#include <unordered_map>

#include "absl/memory/memory.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/server/oak_runtime.h"

namespace oak {

class DevOakLoader {
 public:
  DevOakLoader();

  grpc::Status CreateApplication(const oak::ApplicationConfiguration& application_configuration);

  grpc::Status TerminateApplication();

 private:
  void InitializeAssertionAuthorities();

  // Runtime of the loaded Oak application.
  std::unique_ptr<oak::OakRuntime> runtime_;
};

}  // namespace oak

#endif  // OAK_SERVER_DEV_DEV_OAK_LOADER_H_
