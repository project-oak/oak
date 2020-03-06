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

#include "examples/abitest/client/grpctest.h"

#include "include/grpcpp/grpcpp.h"
#include "oak/common/logging.h"

using ::oak::examples::abitest::GrpcTestRequest;
using ::oak::examples::abitest::GrpcTestResponse;
using ::oak::examples::abitest::OakABITestService;

// Simple manual test case registry.
const std::map<std::string, GrpcTestFn> grpc_tests = {
    {"UnaryMethodOK", test_unary_method_ok},
    {"UnaryMethodErr", test_unary_method_err},
    {"ServerStreamingMethodOK", test_server_streaming_method_ok},
    {"ServerStreamingMethodErr", test_server_streaming_method_err},
    // TODO(#97): add tests for client-streaming methods when implemented.
    {"DISABLED_ClientStreamingMethodOK", test_client_streaming_method_ok},
    {"DISABLED_ClientStreamingMethodErr", test_client_streaming_method_err},
    {"DISABLED_BidiStreamingMethodOK", test_bidi_streaming_method_ok},
    {"DISABLED_BidiStreamingMethodErr", test_bidi_streaming_method_err},
};

bool test_unary_method_ok(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_ok_text("test");
  GrpcTestResponse rsp;
  grpc::Status status = stub->UnaryMethod(&context, req, &rsp);
  if (!status.ok() || (rsp.text() != req.ok_text())) {
    return false;
  }
  return true;
}

bool test_unary_method_err(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_err_code(grpc::FAILED_PRECONDITION);
  GrpcTestResponse rsp;
  grpc::Status status = stub->UnaryMethod(&context, req, &rsp);
  if (status.ok() || (status.error_code() != req.err_code())) {
    return false;
  }
  return true;
}

bool test_server_streaming_method_ok(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_ok_text("test");

  auto reader = stub->ServerStreamingMethod(&context, req);
  if (reader == nullptr) {
    OAK_LOG(QFATAL) << "Could not get response reader";
  }
  int count = 0;
  GrpcTestResponse rsp;
  while (reader->Read(&rsp)) {
    if (rsp.text() != req.ok_text()) {
      return false;
    }
    count++;
  }
  grpc::Status status = reader->Finish();
  if (!status.ok() || (count != 2)) {
    return false;
  }
  return true;
}

bool test_server_streaming_method_err(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_err_code(grpc::FAILED_PRECONDITION);

  auto reader = stub->ServerStreamingMethod(&context, req);
  if (reader == nullptr) {
    OAK_LOG(QFATAL) << "Could not get response reader";
  }
  int count = 0;
  GrpcTestResponse rsp;
  while (reader->Read(&rsp)) {
    count++;
  }
  grpc::Status status = reader->Finish();
  if (status.ok() || (status.error_code() != req.err_code()) || (count != 0)) {
    return false;
  }
  return true;
}

bool test_client_streaming_method_ok(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_ok_text("test");

  GrpcTestResponse rsp;
  auto writer = stub->ClientStreamingMethod(&context, &rsp);
  writer->Write(req);
  writer->Write(req);
  writer->WritesDone();
  grpc::Status status = writer->Finish();
  if (!status.ok() || (rsp.text() != "testtest")) {
    return false;
  }
  return true;
}

bool test_client_streaming_method_err(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_err_code(grpc::FAILED_PRECONDITION);

  GrpcTestResponse rsp;
  auto writer = stub->ClientStreamingMethod(&context, &rsp);
  writer->Write(req);
  writer->WritesDone();
  grpc::Status status = writer->Finish();
  if (status.ok() || (status.error_code() != req.err_code())) {
    return false;
  }
  return true;
}

bool test_bidi_streaming_method_ok(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_ok_text("test");

  auto stream = stub->BidiStreamingMethod(&context);
  stream->Write(req);
  stream->Write(req);
  stream->WritesDone();
  int count = 0;
  GrpcTestResponse rsp;
  while (stream->Read(&rsp)) {
    if (rsp.text() != req.ok_text()) {
      return false;
    }
    count++;
  }
  grpc::Status status = stream->Finish();
  if (!status.ok() || (count != 2)) {
    return false;
  }
  return true;
}

bool test_bidi_streaming_method_err(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_err_code(grpc::FAILED_PRECONDITION);

  auto stream = stub->BidiStreamingMethod(&context);
  stream->Write(req);
  stream->WritesDone();
  int count = 0;
  GrpcTestResponse rsp;
  while (stream->Read(&rsp)) {
    count++;
  }
  grpc::Status status = stream->Finish();
  if (status.ok() || (status.error_code() != req.err_code()) || (count != 0)) {
    return false;
  }
  return true;
}
