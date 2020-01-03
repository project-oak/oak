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

#ifndef OAK_SERVER_ASYLO_ASYLO_OAK_MANAGER_H_
#define OAK_SERVER_ASYLO_ASYLO_OAK_MANAGER_H_

#include <string>

#include "asylo_oak_loader.h"

#include "absl/strings/string_view.h"
#include "asylo/client.h"
#include "asylo/grpc/util/enclave_server.pb.h"
#include "asylo/util/logging.h"
#include "oak/proto/enclave.pb.h"
#include "oak/proto/manager.grpc.pb.h"

namespace oak {

class AsyloOakManager final : public Manager::Service {
 public:
  explicit AsyloOakManager(absl::string_view enclave_path);

  grpc::Status CreateApplication(grpc::ServerContext* context,
                                 const CreateApplicationRequest* request,
                                 CreateApplicationResponse* response) override;

  grpc::Status TerminateApplication(grpc::ServerContext* context,
                                    const TerminateApplicationRequest* request,
                                    TerminateApplicationResponse* response) override;

 private:
  oak::AsyloOakLoader loader_;
};

}  // namespace oak

#endif  // OAK_SERVER_ASYLO_ASYLO_OAK_MANAGER_H_
