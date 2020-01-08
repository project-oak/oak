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

#include <cstdlib>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/memory/memory.h"
#include "absl/strings/match.h"
#include "asylo/util/logging.h"
#include "examples/abitest/client/config.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "google/protobuf/text_format.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/app_config.h"
#include "oak/common/utils.h"
#include "oak/proto/manager.grpc.pb.h"

ABSL_FLAG(std::string, manager_address, "127.0.0.1:8888",
          "Address of the Oak Manager to connect to");
ABSL_FLAG(std::vector<std::string>, module, std::vector<std::string>{},
          "Files containing the compiled WebAssembly modules (as 'frontend,backend')");
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
  int rc = EXIT_SUCCESS;
  absl::ParseCommandLine(argc, argv);

  std::vector<std::string> modules = absl::GetFlag(FLAGS_module);
  if (modules.size() < 2) {
    LOG(QFATAL) << "Need --module=backend,frontend flag";
  }

  // Connect to the Oak Manager.
  auto channel =
      grpc::CreateChannel(absl::GetFlag(FLAGS_manager_address), grpc::InsecureChannelCredentials());
  auto manager_stub = oak::Manager::NewStub(channel, grpc::StubOptions());

  // Load the Oak Modules to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string frontend_module_bytes = oak::utils::read_file(modules[0]);
  std::string backend_module_bytes = oak::utils::read_file(modules[1]);

  // Build an application configuration with two Wasm nodes.
  auto config = absl::make_unique<oak::ApplicationConfiguration>();
  google::protobuf::TextFormat::MergeFromString(app_config_textproto, config.get());

  // Add the Wasm module bytes to the config.
  for (auto& node_config : *config->mutable_node_configs()) {
    if (node_config.name() == "frontend-config") {
      node_config.mutable_wasm_config()->set_module_bytes(frontend_module_bytes);
    } else if (node_config.name() == "backend-config") {
      node_config.mutable_wasm_config()->set_module_bytes(backend_module_bytes);
    }
  }
  if (!ValidApplicationConfig(*config)) {
    LOG(QFATAL) << "Application config is not valid";
  }

  grpc::ClientContext create_ctx;
  oak::CreateApplicationRequest create_req;
  oak::CreateApplicationResponse create_rsp;
  create_req.set_allocated_application_configuration(config.release());

  LOG(INFO) << "Creating multi-Node Oak Application";
  grpc::Status status = manager_stub->CreateApplication(&create_ctx, create_req, &create_rsp);
  if (!status.ok()) {
    LOG(QFATAL) << "Failed: " << status.error_code() << '/' << status.error_message() << '/'
                << status.error_details();
  }

  std::stringstream addr;
  addr << "127.0.0.1:" << create_rsp.grpc_port();
  std::string application_id(create_rsp.application_id());
  LOG(INFO) << "Connecting to Oak Application id=" << application_id << ": " << addr.str();

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = OakABITestService::NewStub(oak::ApplicationClient::CreateChannel(addr.str()));

  // Invoke the application.
  if (!run_tests(stub.get(), absl::GetFlag(FLAGS_test_include),
                 absl::GetFlag(FLAGS_test_exclude))) {
    rc = EXIT_FAILURE;
  }

  // Request termination of the Oak Application.
  LOG(INFO) << "Terminating application id=" << application_id;
  grpc::ClientContext term_ctx;
  oak::TerminateApplicationRequest term_req;
  oak::TerminateApplicationResponse term_rsp;
  term_req.set_application_id(application_id);

  LOG(INFO) << "Terminating Oak Application";
  status = manager_stub->TerminateApplication(&term_ctx, term_req, &term_rsp);
  if (!status.ok()) {
    LOG(ERROR) << "Termination failed: " << status.error_code() << '/' << status.error_message()
               << '/' << status.error_details();
    rc = EXIT_FAILURE;
  }

  return rc;
}
