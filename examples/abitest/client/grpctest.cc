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

#include <thread>
#include <vector>

#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"

using ::oak::examples::abitest::GrpcTestRequest;
using ::oak::examples::abitest::GrpcTestResponse;
using ::oak::examples::abitest::OakABITestService;

// Simple manual test case registry.
const std::map<std::string, GrpcTestFn> grpc_tests = {
    {"GrpcServerUnaryMethodOK", test_unary_method_ok},
    {"GrpcServerUnaryMethodErr", test_unary_method_err},
    {"GrpcServerServerStreamingMethodOK", test_server_streaming_method_ok},
    {"GrpcServerServerStreamingMethodErr", test_server_streaming_method_err},
    // TODO(#97): add tests for client-streaming methods when implemented.
    {"DISABLED_GrpcServerClientStreamingMethodOK", test_client_streaming_method_ok},
    {"DISABLED_GrpcServerClientStreamingMethodErr", test_client_streaming_method_err},
    {"DISABLED_GrpcServerBidiStreamingMethodOK", test_bidi_streaming_method_ok},
    {"DISABLED_GrpcServerBidiStreamingMethodErr", test_bidi_streaming_method_err},
    {"GrpcServerUnaryMethodSlow", test_slow_unary_method},
    {"GrpcServerServerStreamingMethodSlow", test_slow_streaming_method},
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
    LOG(FATAL) << "Could not get response reader";
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
    LOG(FATAL) << "Could not get response reader";
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

bool approximately_equal(absl::Duration left, absl::Duration right) {
  double l = absl::ToDoubleMilliseconds(left);
  double r = absl::ToDoubleMilliseconds(right);
  return (l*0.8 < r && r <  l*1.2);
}

bool test_slow_unary_method(OakABITestService::Stub* stub) {
  bool success = true;
  absl::Mutex mu;

  std::vector<std::thread> threads;
  for (int ii = 0; ii < 3; ii++) {
    threads.push_back(std::thread([stub, ii, &success, &mu]() {
      LOG(INFO) << "Invoke slow method " << ii;
      grpc::ClientContext context;
      GrpcTestRequest req;
      req.set_ok_text("test");
      GrpcTestResponse rsp;
      absl::Time start = absl::Now();
      grpc::Status status = stub->SlowUnaryMethod(&context, req, &rsp);
      absl::Duration duration = (absl::Now() - start);
      LOG(INFO) << "Slow method " << ii << " took " << duration;
      if (!approximately_equal(duration, absl::Seconds(5))) {
        LOG(ERROR) << "Slow method took " << duration << ", expected ~5s";
        absl::MutexLock with(&mu);
        success = false;
      }
    }));
  }
  for (auto& t : threads) {
    t.join();
  }
  return success;
}

bool test_slow_streaming_method(OakABITestService::Stub* stub) {
  grpc::ClientContext context;
  GrpcTestRequest req;
  req.set_ok_text("test");

  absl::Time start = absl::Now();
  auto reader = stub->SlowStreamingMethod(&context, req);
  if (reader == nullptr) {
    LOG(FATAL) << "Could not get response reader";
  }
  bool success = true;
  int count = 0;
  GrpcTestResponse rsp;
  absl::Time prev = start;
  while (reader->Read(&rsp)) {
    absl::Time now = absl::Now();
    absl::Duration total_duration = (now - start);
    absl::Duration duration = (now - prev);
    prev = now;
    count++;
    LOG(INFO) << "Response " << count << " received after " << total_duration
              << " since initial request, " << duration << " since previous activity";
    if (!approximately_equal(duration, absl::Seconds(5))) {
      LOG(ERROR) << "Slow method took " << duration << ", expected ~5s";
      success = false;
    }
  }
  grpc::Status status = reader->Finish();
  return success && status.ok();
}
