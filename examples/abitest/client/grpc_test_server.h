/*
 * Copyright 2020 The Project Oak Authors
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

#ifndef EXAMPLES_ABITEST_CLIENT_GRPC_TEST_SERVER_H
#define EXAMPLES_ABITEST_CLIENT_GRPC_TEST_SERVER_H

#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "include/grpcpp/grpcpp.h"

namespace oak {
namespace test {

class GrpcTestServer final : public ::oak::examples::abitest::OakABITestService::Service {
 public:
  explicit GrpcTestServer() {}

  grpc::Status RunTests(grpc::ServerContext* context,
                        const oak::examples::abitest::ABITestRequest* req,
                        oak::examples::abitest::ABITestResponse* rsp) override;

  grpc::Status UnaryMethod(grpc::ServerContext* context,
                           const oak::examples::abitest::GrpcTestRequest* req,
                           oak::examples::abitest::GrpcTestResponse* rsp) override;

  grpc::Status ServerStreamingMethod(
      grpc::ServerContext* context, const oak::examples::abitest::GrpcTestRequest* req,
      grpc::ServerWriter<oak::examples::abitest::GrpcTestResponse>* writer) override;

  grpc::Status ClientStreamingMethod(
      grpc::ServerContext* context,
      grpc::ServerReader<oak::examples::abitest::GrpcTestRequest>* reader,
      oak::examples::abitest::GrpcTestResponse* rsp) override;

  grpc::Status BidiStreamingMethod(
      ::grpc::ServerContext* context,
      grpc::ServerReaderWriter<oak::examples::abitest::GrpcTestResponse,
                               oak::examples::abitest::GrpcTestRequest>* stream) override;

  grpc::Status SlowUnaryMethod(grpc::ServerContext* context,
                               const oak::examples::abitest::GrpcTestRequest* req,
                               oak::examples::abitest::GrpcTestResponse* rsp) override;

  grpc::Status SlowStreamingMethod(
      grpc::ServerContext* context, const oak::examples::abitest::GrpcTestRequest* req,
      grpc::ServerWriter<oak::examples::abitest::GrpcTestResponse>* writer) override;
};

}  // namespace test
}  // namespace oak

#endif  // EXAMPLES_ABITEST_CLIENT_GRPC_TEST_SERVER_H
