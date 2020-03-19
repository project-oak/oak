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
#include <thread>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/strings/match.h"
#include "examples/abitest/client/grpc_test_server.h"
#include "examples/abitest/client/grpctest.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/logging.h"
#include "oak/server/storage/memory_provider.h"
#include "oak/server/storage/storage_service.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");
ABSL_FLAG(int, storage_port, 7867,
          "Port on which the test Storage Server listens; set to zero to disable.");
ABSL_FLAG(int, grpc_test_port, 7878,
          "Port on which the test gRPC Server listens; set to zero to disable.");
ABSL_FLAG(bool, test_abi, true, "Whether to perform ABI tests");
ABSL_FLAG(bool, test_grpc, true, "Whether to perform gRPC tests");
ABSL_FLAG(std::string, test_include, "", "Filter indicating which tests to include");
ABSL_FLAG(std::string, test_exclude, "", "Filter indicating tests to exclude (if nonempty)");

using ::oak::examples::abitest::ABITestRequest;
using ::oak::examples::abitest::ABITestResponse;
using ::oak::examples::abitest::OakABITestService;

namespace {

// Run Oak ABI tests, by sending a request to the abitest Oak Application which
// then runs a collection of tests of the ABI inside Oak and reports the results.
bool run_abi_tests(OakABITestService::Stub* stub, const std::string& include,
                   const std::string& exclude) {
  OAK_LOG(INFO) << "Run ABI tests matching: '" << include << "', exclude those matching '"
                << exclude << "'";
  grpc::ClientContext context;
  ABITestRequest request;
  request.set_include(include);
  request.set_exclude(exclude);
  ABITestResponse response;
  grpc::Status status = stub->RunTests(&context, request, &response);
  if (!status.ok()) {
    OAK_LOG(WARNING) << "Could not call RunTests('" << include << "'): " << status.error_code()
                     << ": " << status.error_message();
    return false;
  }

  bool success = true;
  int disabled = 0;
  for (const auto& result : response.results()) {
    if (result.disabled()) {
      disabled++;
      continue;
    }
    OAK_LOG(INFO) << "[ " << (result.success() ? " OK " : "FAIL") << " ] " << result.name();
    if (!result.success()) {
      success = false;
      OAK_LOG(INFO) << "    Details: " << result.details();
    }
  }
  if (disabled > 0) {
    OAK_LOG(INFO) << " YOU HAVE " << disabled << " DISABLED ABI TEST"
                  << ((disabled > 1) ? "S" : "");
  }
  return success;
}

// Run tests of the gRPC connection to an Oak Application, including error
// propagation and different types of method (client/server streaming).
bool run_grpc_tests(OakABITestService::Stub* stub, const std::string& include,
                    const std::string& exclude) {
  OAK_LOG(INFO) << "Run gRPC tests matching: '" << include << "', exclude those matching '"
                << exclude << "'";
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
      OAK_LOG(INFO) << "[  OK  ] " << test_name;
    } else {
      success = false;
      OAK_LOG(INFO) << "[ FAIL ] " << test_name;
    }
  }
  if (disabled > 0) {
    OAK_LOG(INFO) << " YOU HAVE " << disabled << " DISABLED GRPC TEST"
                  << ((disabled > 1) ? "S" : "");
  }

  return success;
}

void run_storage_server(int storage_port, grpc::Server** storage_server) {
  OAK_LOG(INFO) << "Creating in-memory storage service on :" << storage_port;
  grpc::ServerBuilder builder;
  std::string server_address = absl::StrCat("[::]:", storage_port);
  std::shared_ptr<grpc::ServerCredentials> credentials = grpc::InsecureServerCredentials();
  builder.AddListeningPort(server_address, credentials);
  oak::StorageService storage_service(new oak::MemoryProvider());
  builder.RegisterService(&storage_service);

  OAK_LOG(INFO) << "Start storage server";
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  *storage_server = server.get();
  server->Wait();
  OAK_LOG(INFO) << "Storage server done";
}

void run_grpc_test_server(int grpc_test_port, grpc::Server** grpc_test_server) {
  OAK_LOG(INFO) << "Creating test gRPC service on :" << grpc_test_port;
  grpc::ServerBuilder builder;
  std::string server_address = absl::StrCat("[::]:", grpc_test_port);
  std::shared_ptr<grpc::ServerCredentials> credentials = grpc::InsecureServerCredentials();
  builder.AddListeningPort(server_address, credentials);

  oak::test::GrpcTestServer grpc_test_service;
  builder.RegisterService(&grpc_test_service);

  OAK_LOG(INFO) << "Start test gRPC server";
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  *grpc_test_server = server.get();
  server->Wait();
  OAK_LOG(INFO) << "Test gRPC server done";
}

}  // namespace

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  int storage_port = absl::GetFlag(FLAGS_storage_port);
  std::unique_ptr<std::thread> storage_thread;
  grpc::Server* storage_server;
  if (storage_port > 0) {
    storage_thread =
        absl::make_unique<std::thread>(run_storage_server, storage_port, &storage_server);
  }

  int grpc_test_port = absl::GetFlag(FLAGS_grpc_test_port);
  std::unique_ptr<std::thread> grpc_test_thread;
  grpc::Server* grpc_test_server;
  if (grpc_test_port > 0) {
    grpc_test_thread =
        absl::make_unique<std::thread>(run_grpc_test_server, grpc_test_port, &grpc_test_server);
  }

  const std::string& include = absl::GetFlag(FLAGS_test_include);
  const std::string& exclude = absl::GetFlag(FLAGS_test_exclude);

  // Connect to the Oak Application.
  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  OAK_LOG(INFO) << "Connecting to Oak Application: " << address;

  auto stub =
      OakABITestService::NewStub(oak::ApplicationClient::CreateTlsChannel(address, ca_cert));

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

  if (storage_thread != nullptr) {
    storage_server->Shutdown(std::chrono::system_clock::now() + std::chrono::milliseconds(100));
    storage_thread->join();
  }

  if (grpc_test_thread != nullptr) {
    grpc_test_server->Shutdown(std::chrono::system_clock::now() + std::chrono::milliseconds(100));
    grpc_test_thread->join();
  }

  return (success ? EXIT_SUCCESS : EXIT_FAILURE);
}
