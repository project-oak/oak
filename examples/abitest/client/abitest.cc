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

#include <map>
#include <regex>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/strings/match.h"
#include "asylo/util/logging.h"
#include "examples/abitest/client/grpctest.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(bool, test_abi, true, "Whether to perform ABI tests");
ABSL_FLAG(bool, test_grpc, true, "Whether to perform gRPC tests");
ABSL_FLAG(std::string, test_include, "", "Filter indicating which tests to include");
// Exclude 'Storage' test by default because it requires an external storage server.
ABSL_FLAG(std::string, test_exclude, "^Storage$",
          "Filter indicating tests to exclude (if nonempty)");

using ::oak::examples::abitest::ABITestRequest;
using ::oak::examples::abitest::ABITestResponse;
using ::oak::examples::abitest::OakABITestService;

namespace {

// Run Oak ABI tests, by sending a request to the abitest Oak Application which
// then runs a collection of tests of the ABI inside Oak and reports the results.
bool run_abi_tests(OakABITestService::Stub* stub, const std::string& include,
                   const std::string& exclude) {
  LOG(INFO) << "Run ABI tests matching: '" << include << "', exclude those matching '" << exclude
            << "'";
  grpc::ClientContext context;
  ABITestRequest request;
  request.set_include(include);
  request.set_exclude(exclude);
  ABITestResponse response;
  grpc::Status status = stub->RunTests(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not call RunTests('" << include << "'): " << status.error_code() << ": "
                 << status.error_message();
    return false;
  }

  bool success = true;
  int disabled = 0;
  for (const auto& result : response.results()) {
    if (result.disabled()) {
      disabled++;
      continue;
    }
    LOG(INFO) << "[ " << (result.success() ? " OK " : "FAIL") << " ] " << result.name();
    if (!result.success()) {
      success = false;
      LOG(INFO) << "    Details: " << result.details();
    }
  }
  if (disabled > 0) {
    LOG(INFO) << " YOU HAVE " << disabled << " DISABLED ABI TEST" << ((disabled > 1) ? "S" : "");
  }
  return success;
}

// Run tests of the gRPC connection to an Oak Application, including error
// propagation and different types of method (client/server streaming).
bool run_grpc_tests(OakABITestService::Stub* stub, const std::string& include,
                    const std::string& exclude) {
  LOG(INFO) << "Run gRPC tests matching: '" << include << "', exclude those matching '" << exclude
            << "'";
  bool success = true;
  std::regex include_re(include);
  std::regex exclude_re(exclude);
  int disabled = 0;
  for (const auto& test : grpc_tests) {
    const std::string& test_name = test.first;
    GrpcTestFn test_fn = test.second;
    if (!std::regex_search(test_name, include_re)) {
      continue;
    }
    if (!exclude.empty() && std::regex_search(test_name, exclude_re)) {
      continue;
    }
    if (absl::StartsWith(test_name, "DISABLED_")) {
      disabled++;
      continue;
    }

    if (test_fn(stub)) {
      LOG(INFO) << "[  OK  ] " << test_name;
    } else {
      success = false;
      LOG(INFO) << "[ FAIL ] " << test_name;
    }
  }
  if (disabled > 0) {
    LOG(INFO) << " YOU HAVE " << disabled << " DISABLED GRPC TEST" << ((disabled > 1) ? "S" : "");
  }

  return success;
}

}  // namespace

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);
  const std::string& include = absl::GetFlag(FLAGS_test_include);
  const std::string& exclude = absl::GetFlag(FLAGS_test_exclude);

  // Connect to the Oak Application.
  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;
  oak::ApplicationClient::InitializeAssertionAuthorities();
  auto stub = OakABITestService::NewStub(oak::ApplicationClient::CreateChannel(address));

  bool success = true;
  if (absl::GetFlag(FLAGS_test_abi)) {
    // Invoke the RunTests method of the Application.
    if (!run_abi_tests(stub.get(), include, exclude)) {
      success = false;
    }
  }

  if (absl::GetFlag(FLAGS_test_grpc)) {
    // Test gRPC modes.
    if (!run_grpc_tests(stub.get(), include, exclude)) {
      success = false;
    }
  }

  return (success ? EXIT_SUCCESS : EXIT_FAILURE);
}
