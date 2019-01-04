/*
 * Copyright 2018 Tha Project Oak Authors
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

#include "oak/proto/oak_server.grpc.pb.h"

#include "src/interp/interp.h"

namespace oak {
namespace grpc_server {

class OakServer final : public ::oak::OakServer::Service {
 public:
  OakServer();

 private:
  ::grpc::Status InitiateComputation(::grpc::ServerContext *context,
                                     const ::oak::InitiateComputationRequest *request,
                                     ::oak::InitiateComputationResponse *response) override;

  void InitEnvironment(wabt::interp::Environment *env);
  ::wabt::interp::HostFunc::Callback OakRead(wabt::interp::Environment *env);

  std::vector<std::vector<char>> in_buckets;
  std::vector<uint32_t> in_cursors;

  std::vector<std::vector<char>> out_buckets;
  std::vector<uint32_t> out_cursors;
};

}  // namespace grpc_server
}  // namespace oak
