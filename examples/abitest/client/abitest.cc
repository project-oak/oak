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
#include "absl/memory/memory.h"
#include "absl/strings/match.h"
#include "asylo/util/logging.h"
#include "examples/abitest/proto/abitest.grpc.pb.h"
#include "examples/abitest/proto/abitest.pb.h"
#include "examples/utils/utils.h"
#include "google/protobuf/text_format.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/app_config.h"
#include "oak/proto/manager.grpc.pb.h"

ABSL_FLAG(std::string, manager_address, "127.0.0.1:8888",
          "Address of the Oak Manager to connect to");
ABSL_FLAG(std::vector<std::string>, module, std::vector<std::string>{},
          "Files containing the compiled WebAssembly modules (as 'backend,frontend')");
ABSL_FLAG(std::string, test_filter, "", "Filter indicating which tests to run");

using ::oak::examples::abitest::ABITestRequest;
using ::oak::examples::abitest::ABITestResponse;
using ::oak::examples::abitest::OakABITestService;

// Application config as text proto. Deliberately use non-default names for
// nodes and ports to confirm that nothing has been accidentally hard-coded.
static const char* app_config_textproto = R"raw(nodes {
  node_name: "frontend"
  web_assembly_node {
    wasm_contents_name: "frontend-code"
    ports {
      name: "gRPC_input"
      type: IN
    }
    ports {
      name: "logging_port"
      type: OUT
    }
    ports {
      name: "to_backend_0"
      type: OUT
    }
    ports {
      name: "from_backend_0"
      type: IN
    }
    ports {
      name: "to_backend_1"
      type: OUT
    }
    ports {
      name: "from_backend_1"
      type: IN
    }
    ports {
      name: "to_backend_2"
      type: OUT
    }
    ports {
      name: "from_backend_2"
      type: IN
    }
  }
}
nodes {
  node_name: "backend_0"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "backend_1"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "backend_2"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "grpc_server"
  grpc_server_node {}
}
nodes {
  node_name: "logging_node"
  log_node {}
}
wasm_contents {
  name: "frontend-code"
  module_bytes: "<filled in later>"
}
wasm_contents {
  name: "backend-code"
  module_bytes: "<filled in later>"
}
channels {
  source_endpoint {
    node_name: "grpc_server"
    port_name: "request"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "gRPC_input"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_0"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_1"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_2"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_0"
  }
  destination_endpoint {
    node_name: "backend_0"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_0"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_0"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_1"
  }
  destination_endpoint {
    node_name: "backend_1"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_1"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_1"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_2"
  }
  destination_endpoint {
    node_name: "backend_2"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_2"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_2"
  }
}
)raw";

static bool run_tests(OakABITestService::Stub* stub, const std::string& filter) {
  grpc::ClientContext context;
  ABITestRequest request;
  request.set_filter(filter);
  LOG(INFO) << "Run tests matching: '" << filter << "'";
  ABITestResponse response;
  grpc::Status status = stub->RunTests(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not call RunTests('" << filter << "'): " << status.error_code() << ": "
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
  int rc = 0;
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
  std::string backend_module_bytes = oak::utils::read_file(modules[0]);
  std::string frontend_module_bytes = oak::utils::read_file(modules[1]);

  // Build an application configuration with two Wasm nodes.
  auto config = absl::make_unique<oak::ApplicationConfiguration>();
  google::protobuf::TextFormat::MergeFromString(app_config_textproto, config.get());

  // Add the Wasm module bytes to the config.
  for (auto& contents : *config->mutable_wasm_contents()) {
    if (contents.name() == "frontend-code") {
      contents.set_module_bytes(frontend_module_bytes);
    } else if (contents.name() == "backend-code") {
      contents.set_module_bytes(backend_module_bytes);
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
  if (!run_tests(stub.get(), absl::GetFlag(FLAGS_test_filter))) {
    rc = 1;
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
    rc = 1;
  }

  return rc;
}
