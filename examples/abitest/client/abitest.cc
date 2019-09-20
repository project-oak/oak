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

using ::oak::examples::abitest::ExampleRequest;
using ::oak::examples::abitest::ExampleResponse;
using ::oak::examples::abitest::ExampleService;

// Application config as text proto. Deliberately use non-default names for
// nodes and ports to confirm that nothing has been accidentally hard-coded.
static const char* app_config_textproto = R"raw(nodes {
  node_name: "frontend"
  web_assembly_node {
    module_bytes: "<filled in later>"
    ports {
      name: "gRPC_input"
      type: IN
    }
    ports {
      name: "gRPC_output"
      type: OUT
    }
    ports {
      name: "logging_port"
      type: OUT
    }
    ports {
      name: "to_backend"
      type: OUT
    }
    ports {
      name: "from_backend"
      type: IN
    }
  }
}
nodes {
  node_name: "backend"
  web_assembly_node {
    module_bytes: "<filled in later>"
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
    port_name: "gRPC_output"
  }
  destination_endpoint {
    node_name: "grpc_server"
    port_name: "response"
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
    node_name: "backend"
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
    port_name: "to_backend"
  }
  destination_endpoint {
    node_name: "backend"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend"
  }
}
)raw";

static void example_method(ExampleService::Stub* stub, const std::string& name) {
  grpc::ClientContext context;
  ExampleRequest request;
  request.set_greeting(name);
  LOG(INFO) << "Request: " << request.greeting();
  ExampleResponse response;
  grpc::Status status = stub->ExampleMethod(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not call ExampleMethod('" << name << "'): " << status.error_code()
                 << ": " << status.error_message();
    return;
  }
  LOG(INFO) << "Response: " << response.reply();
}

int main(int argc, char** argv) {
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
  for (auto& node : *config->mutable_nodes()) {
    if (!node.has_web_assembly_node()) {
      continue;
    }
    if (node.node_name() == "frontend") {
      node.mutable_web_assembly_node()->set_module_bytes(frontend_module_bytes);
    } else if (node.node_name() == "backend") {
      node.mutable_web_assembly_node()->set_module_bytes(backend_module_bytes);
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
  auto stub = ExampleService::NewStub(grpc::CreateChannel(
      addr.str(), asylo::EnclaveChannelCredentials(asylo::BidirectionalNullCredentialsOptions())));

  // Invoke the application.
  example_method(stub.get(), "WORLD");

  // Request termination of the Oak Application.
  LOG(INFO) << "Terminating application id=" << application_id;
  grpc::ClientContext term_ctx;
  oak::TerminateApplicationRequest term_req;
  oak::TerminateApplicationResponse term_rsp;
  term_req.set_application_id(application_id);

  LOG(INFO) << "Terminating Oak Application";
  status = manager_stub->TerminateApplication(&term_ctx, term_req, &term_rsp);
  if (!status.ok()) {
    LOG(ERROR) << "Failed: " << status.error_code() << '/' << status.error_message() << '/'
               << status.error_details();
  }

  return 0;
}
