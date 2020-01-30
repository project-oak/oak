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
#include "asylo/util/logging.h"
#include "examples/translator/proto/translator.grpc.pb.h"
#include "examples/translator/proto/translator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/client/manager_client.h"
#include "oak/common/utils.h"

ABSL_FLAG(std::string, manager_address, "127.0.0.1:8888",
          "Address of the Oak Manager to connect to");
ABSL_FLAG(std::string, module, "", "File containing the compiled WebAssembly module");

using ::oak::examples::translator::TranslateRequest;
using ::oak::examples::translator::TranslateResponse;
using ::oak::examples::translator::Translator;

void translate(Translator::Stub* stub, const std::string& text, const std::string& from_lang,
               const std::string& to_lang) {
  grpc::ClientContext context;
  TranslateRequest request;
  request.set_text(text);
  request.set_from_lang(from_lang);
  request.set_to_lang(to_lang);

  LOG(INFO) << "Translate '" << request.text() << "' from " << from_lang << " to " << to_lang;
  TranslateResponse response;
  grpc::Status status = stub->Translate(&context, request, &response);
  if (!status.ok()) {
    LOG(WARNING) << "Could not perform Translate('" << text << "', " << from_lang << "=>" << to_lang
                 << "): " << status.error_code() << ": " << status.error_message();
    return;
  }
  LOG(INFO) << "Response: " << response.translated_text();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  // Connect to the Oak Manager.
  std::unique_ptr<oak::ManagerClient> manager_client =
      absl::make_unique<oak::ManagerClient>(grpc::CreateChannel(
          absl::GetFlag(FLAGS_manager_address), grpc::InsecureChannelCredentials()));

  // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly separately.
  std::string module_bytes = oak::utils::read_file(absl::GetFlag(FLAGS_module));
  std::unique_ptr<oak::CreateApplicationResponse> create_application_response =
      manager_client->CreateApplication(module_bytes, /* logging= */ true,
                                        /* storage_address= */ "");
  if (create_application_response == nullptr) {
    LOG(QFATAL) << "Failed to create application";
  }

  std::stringstream addr;
  addr << "127.0.0.1:" << create_application_response->grpc_port();
  std::string application_id(create_application_response->application_id());
  LOG(INFO) << "Connecting to Oak Application id=" << application_id << ": " << addr.str();

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = Translator::NewStub(oak::ApplicationClient::CreateChannel(addr.str()));

  translate(stub.get(), "WORLDS", "en", "fr");
  translate(stub.get(), "WORLDS", "en", "it");
  translate(stub.get(), "WORLDS", "en", "cn");
  translate(stub.get(), "OSSIFRAGE", "en", "fr");

  // Request termination of the Oak Application.
  LOG(INFO) << "Terminating application id=" << application_id;
  manager_client->TerminateApplication(application_id);

  return EXIT_SUCCESS;
}
