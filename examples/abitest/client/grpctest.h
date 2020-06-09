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

#ifndef EXAMPLES_ABITEST_CLIENT_GRPCTEST_H
#define EXAMPLES_ABITEST_CLIENT_GRPCTEST_H

#include <map>
#include <string>

#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"

// Test functions return true on success, false on failure.
typedef bool (*GrpcTestFn)(oak::examples::abitest::OakABITestService::Stub*);
extern const std::map<std::string, GrpcTestFn> grpc_tests;

bool test_unary_method_ok(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_unary_method_err(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_server_streaming_method_ok(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_server_streaming_method_err(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_client_streaming_method_ok(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_client_streaming_method_err(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_bidi_streaming_method_ok(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_bidi_streaming_method_err(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_slow_unary_method(oak::examples::abitest::OakABITestService::Stub* stub);
bool test_slow_streaming_method(oak::examples::abitest::OakABITestService::Stub* stub);

#endif  // EXAMPLES_ABITEST_CLIENT_GRPCTEST_H
