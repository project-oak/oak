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

#include "examples/abitest/client/grpc_test_server.h"

#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"

using ::oak::examples::abitest::GrpcTestRequest;
using ::oak::examples::abitest::GrpcTestResponse;

namespace oak {
namespace test {

grpc::Status GrpcTestServer::RunTests(grpc::ServerContext* context,
                                      const oak::examples::abitest::ABITestRequest* req,
                                      oak::examples::abitest::ABITestResponse* rsp) {
  // Test server only implements the gRPC test methods.
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status GrpcTestServer::UnaryMethod(grpc::ServerContext* context, const GrpcTestRequest* req,
                                         GrpcTestResponse* rsp) {
  if (req->method_result_case() == GrpcTestRequest::kErrCode) {
    LOG(INFO) << "UnaryMethod -> Err(" << req->err_code() << ")";
    return grpc::Status(static_cast<grpc::StatusCode>(req->err_code()), "Deliberate error");
  }
  rsp->set_text(req->ok_text());
  LOG(INFO) << "UnaryMethod -> Ok('" << rsp->text() << "')";
  return grpc::Status::OK;
}

grpc::Status GrpcTestServer::ServerStreamingMethod(grpc::ServerContext* context,
                                                   const GrpcTestRequest* req,
                                                   grpc::ServerWriter<GrpcTestResponse>* writer) {
  if (req->method_result_case() == GrpcTestRequest::kErrCode) {
    LOG(INFO) << "ServerStreamingMethod -> Err(" << req->err_code() << ")";
    return grpc::Status(static_cast<grpc::StatusCode>(req->err_code()), "Deliberate error");
  }

  // Write two responses to exercise streaming.
  GrpcTestResponse rsp;
  rsp.set_text(req->ok_text());
  LOG(INFO) << "ServerStreamingMethod -> '" << req->ok_text() << "'";
  writer->Write(rsp);
  LOG(INFO) << "ServerStreamingMethod -> '" << req->ok_text() << "'";
  writer->Write(rsp);
  LOG(INFO) << "ServerStreamingMethod -> OK";
  return grpc::Status::OK;
}

grpc::Status GrpcTestServer::ClientStreamingMethod(grpc::ServerContext* context,
                                                   grpc::ServerReader<GrpcTestRequest>* reader,
                                                   GrpcTestResponse* rsp) {
  // If any request triggers an error, return it.
  std::string combined_text;
  GrpcTestRequest req;
  while (reader->Read(&req)) {
    if (req.method_result_case() == GrpcTestRequest::kErrCode) {
      LOG(INFO) << "ClientStreamingMethod -> Err(" << req.err_code() << ")";
      return grpc::Status(static_cast<grpc::StatusCode>(req.err_code()), "Deliberate error");
    }
    combined_text += req.ok_text();
  }
  rsp->set_text(combined_text);
  LOG(INFO) << "ClientStreamingMethod -> OK('" << rsp->text() << "')";
  return grpc::Status::OK;
}

grpc::Status GrpcTestServer::BidiStreamingMethod(
    ::grpc::ServerContext* context,
    grpc::ServerReaderWriter<GrpcTestResponse, GrpcTestRequest>* stream) {
  GrpcTestRequest req;
  while (stream->Read(&req)) {
    if (req.method_result_case() == GrpcTestRequest::kErrCode) {
      LOG(INFO) << "BidiStreamingMethod -> Err(" << req.err_code() << ")";
      return grpc::Status(static_cast<grpc::StatusCode>(req.err_code()), "Deliberate error");
    }
    GrpcTestResponse rsp;
    rsp.set_text(req.ok_text());
    LOG(INFO) << "BidiStreamingMethod -> '" << rsp.text() << "'";
    stream->Write(rsp);
  }
  LOG(INFO) << "BidiStreamingMethod -> OK";
  return grpc::Status::OK;
}

grpc::Status GrpcTestServer::SlowUnaryMethod(grpc::ServerContext* context,
                                             const GrpcTestRequest* req, GrpcTestResponse* rsp) {
  LOG(INFO) << "UnaryMethod ...";
  absl::SleepFor(absl::Seconds(5));
  rsp->set_text("sloow");
  LOG(INFO) << "UnaryMethod ... -> Ok('" << rsp->text() << "')";
  return grpc::Status::OK;
}

grpc::Status GrpcTestServer::SlowStreamingMethod(grpc::ServerContext* context,
                                                 const GrpcTestRequest* req,
                                                 grpc::ServerWriter<GrpcTestResponse>* writer) {
  // Write two responses to exercise streaming.
  GrpcTestResponse rsp;
  rsp.set_text("sloow");
  LOG(INFO) << "ServerStreamingMethod...";
  absl::SleepFor(absl::Seconds(3));
  writer->Write(rsp);
  LOG(INFO) << "ServerStreamingMethod... -> '" << req->ok_text() << "'";

  LOG(INFO) << "ServerStreamingMethod...";
  absl::SleepFor(absl::Seconds(3));
  writer->Write(rsp);
  LOG(INFO) << "ServerStreamingMethod... -> '" << req->ok_text() << "'";
  LOG(INFO) << "ServerStreamingMethod -> OK";
  return grpc::Status::OK;
}

}  // namespace test
}  // namespace oak
