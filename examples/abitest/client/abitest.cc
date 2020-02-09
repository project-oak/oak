/*
 * Copyright 2019 The Project Oak Authors
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

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "asylo/util/logging.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, test_include, "", "Filter indicating which tests to include");
ABSL_FLAG(std::string, test_exclude, "", "Filter indicating tests to exclude (if nonempty)");

using ::oak::examples::abitest::ABITestRequest;
using ::oak::examples::abitest::ABITestResponse;
using ::oak::examples::abitest::OakABITestService;

static bool run_tests(OakABITestService::Stub* stub, const std::string& include,
                      const std::string& exclude) {
  grpc::ClientContext context;
  ABITestRequest request;
  request.set_include(include);
  request.set_exclude(exclude);
  LOG(INFO) << "Run tests matching: '" << include << "'";
  ABITestResponse response;
  grpc::Status status = stub->RunTests(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not call RunTests('" << include << "'): " << status.error_code() << ": "
                 << status.error_message();
    return false;
  }

  bool success = true;
  for (const auto& result : response.results()) {
    LOG(INFO) << "[ " << (result.success() ? " OK " : "FAIL") << " ] " << result.name();
    if (!result.success()) {
      success = false;
      LOG(INFO) << "    Details: " << result.details();
    }
  }
  return success;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = OakABITestService::NewStub(oak::ApplicationClient::CreateChannel(address));

  // Invoke the application.
  if (!run_tests(stub.get(), absl::GetFlag(FLAGS_test_include),
                 absl::GetFlag(FLAGS_test_exclude))) {
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
