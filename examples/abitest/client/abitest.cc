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
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "examples/abitest/client/grpc_test_server.h"
#include "examples/abitest/client/grpctest.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "glog/logging.h"
#include "httplib.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/server/storage/memory_provider.h"
#include "oak/server/storage/storage_service.h"

ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");
ABSL_FLAG(std::string, private_key, "", "Path to the private key");
ABSL_FLAG(std::string, cert_chain, "", "Path to the PEM-encoded certificate chain");
ABSL_FLAG(int, storage_port, 7867,
          "Port on which the test Storage Server listens; set to zero to disable.");
ABSL_FLAG(int, grpc_test_port, 7878,
          "Port on which the test gRPC Server listens; set to zero to disable.");
ABSL_FLAG(bool, test_abi, true, "Whether to perform ABI tests");
ABSL_FLAG(bool, test_grpc, true, "Whether to perform gRPC tests");
ABSL_FLAG(bool, test_aux, true, "Whether to perform tests on Runtime auxiliary servers");
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

bool check_page(httplib::Client* client, const char* path) {
  LOG(INFO) << "Get aux page at '" << path << "'";
  auto res = client->Get(path);
  if (!res || res->status != 200) {
    LOG(WARNING) << "Request for '" << path << "' failed";
    return false;
  }
  VLOG(1) << "Received for '" << path << "': " << res->body;
  return true;
}

// Test that the Runtime's auxiliary servers respond to various
// paths.
bool run_aux_tests() {
  bool success = true;

  httplib::Client metrics("localhost", 9090);
  success &= check_page(&metrics, "/metrics");
  // Check a failed page.
  success &= !check_page(&metrics, "/boguspath");

  httplib::Client introspect("localhost", 1909);
  success &= check_page(&introspect, "/");
  success &= check_page(&introspect, "/graph");
  success &= check_page(&introspect, "/objcount");
  success &= check_page(&introspect, "/node/0");
  success &= check_page(&introspect, "/node/1");
  // Check some failed pages.
  success &= !check_page(&introspect, "/boguspath");
  success &= !check_page(&introspect, "/node/9999999999");
  success &= !check_page(&introspect, "/node/9999999999/1");

  // Look in the content of a per-Node page to find a valid /node/handle/ link.
  auto res = introspect.Get("/node/1");
  if (res && res->status == 200) {
    // Find the first match for 'href="/node/1/\d+"' in res->body.
    std::string prefix = "href=\"/node/1/";
    size_t found = res->body.find(prefix);
    if (found != std::string::npos) {
      size_t start = found + prefix.size();
      size_t end = res->body.find("\"", start);
      absl::string_view handle_str(res->body.c_str() + start, end - start);
      uint64_t handle;
      if (absl::SimpleAtoi(handle_str, &handle)) {
        success &= check_page(&introspect, absl::StrCat("/node/1/", handle).c_str());
      } else {
        LOG(ERROR) << "Could not parse handle value from '" << handle_str << "'";
        success = false;
      }
    } else {
      LOG(ERROR) << "Could not find link to node-handle page";
      success = false;
    }
  } else {
    success = false;
  }

  return success;
}

void run_storage_server(int storage_port, grpc::Server** storage_server) {
  LOG(INFO) << "Creating in-memory storage service on :" << storage_port;
  grpc::ServerBuilder builder;
  std::string server_address = absl::StrCat("[::]:", storage_port);
  std::shared_ptr<grpc::ServerCredentials> credentials = grpc::InsecureServerCredentials();
  builder.AddListeningPort(server_address, credentials);
  oak::StorageService storage_service(new oak::MemoryProvider());
  builder.RegisterService(&storage_service);

  LOG(INFO) << "Start storage server";
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  *storage_server = server.get();
  server->Wait();
  LOG(INFO) << "Storage server done";
}

void run_grpc_test_server(int grpc_test_port, grpc::Server** grpc_test_server,
                          std::shared_ptr<grpc::ServerCredentials> credentials) {
  LOG(INFO) << "Creating test gRPC service on :" << grpc_test_port;
  grpc::ServerBuilder builder;
  std::string server_address = absl::StrCat("[::]:", grpc_test_port);
  builder.AddListeningPort(server_address, credentials);

  oak::test::GrpcTestServer grpc_test_service;
  builder.RegisterService(&grpc_test_service);

  LOG(INFO) << "Start test gRPC server";
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  *grpc_test_server = server.get();
  server->Wait();
  LOG(INFO) << "Test gRPC server done";
}

}  // namespace

std::shared_ptr<grpc::ServerCredentials> CreateGrpcCredentialsOrDie(const std::string& private_key,
                                                                    const std::string& cert_chain,
                                                                    const std::string& ca_cert) {
  grpc::SslServerCredentialsOptions::PemKeyCertPair key_cert_pair = {private_key, cert_chain};
  grpc::SslServerCredentialsOptions options;
  options.pem_root_certs = ca_cert;
  options.pem_key_cert_pairs.push_back(key_cert_pair);
  return grpc::SslServerCredentials(options);
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  int storage_port = absl::GetFlag(FLAGS_storage_port);
  std::unique_ptr<std::thread> storage_thread;
  grpc::Server* storage_server;
  if (storage_port > 0) {
    storage_thread =
        absl::make_unique<std::thread>(run_storage_server, storage_port, &storage_server);
  }

  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));

  int grpc_test_port = absl::GetFlag(FLAGS_grpc_test_port);
  std::unique_ptr<std::thread> grpc_test_thread;
  grpc::Server* grpc_test_server;

  if (grpc_test_port > 0) {
    std::string private_key_path = absl::GetFlag(FLAGS_private_key);
    std::string cert_chain_path = absl::GetFlag(FLAGS_cert_chain);
    if (private_key_path.empty()) {
      LOG(FATAL) << "No private key file specified";
    }
    if (cert_chain_path.empty()) {
      LOG(FATAL) << "No certificate chain file specified";
    }
    std::string private_key = oak::utils::read_file(private_key_path);
    std::string cert_chain = oak::utils::read_file(cert_chain_path);

    std::shared_ptr<grpc::ServerCredentials> grpc_credentials =
        CreateGrpcCredentialsOrDie(private_key, cert_chain, ca_cert);
    grpc_test_thread = absl::make_unique<std::thread>(run_grpc_test_server, grpc_test_port,
                                                      &grpc_test_server, grpc_credentials);
  }

  const std::string& include = absl::GetFlag(FLAGS_test_include);
  const std::string& exclude = absl::GetFlag(FLAGS_test_exclude);

  // Connect to the Oak Application.
  std::string address = absl::GetFlag(FLAGS_address);
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#1066): Assign a more restrictive label.
  oak::label::Label label = oak::PublicUntrustedLabel();
  // Connect to the Oak Application.
  auto stub = OakABITestService::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

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

  if (absl::GetFlag(FLAGS_test_aux)) {
    // Test auxiliary servers.
    if (!run_aux_tests()) {
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
