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
#include "examples/translator/proto/translator.grpc.pb.h"
#include "examples/translator/proto/translator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/logging.h"

ABSL_FLAG(std::string, address, "127.0.0.1:8080", "Address of the Oak application to connect to");

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

  OAK_LOG(INFO) << "Translate '" << request.text() << "' from " << from_lang << " to " << to_lang;
  TranslateResponse response;
  grpc::Status status = stub->Translate(&context, request, &response);
  if (!status.ok()) {
    OAK_LOG(WARNING) << "Could not perform Translate('" << text << "', " << from_lang << "=>"
                     << to_lang << "): " << status.error_code() << ": " << status.error_message();
    return;
  }
  OAK_LOG(INFO) << "Response: " << response.translated_text();
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  OAK_LOG(INFO) << "Connecting to Oak Application: " << address;

  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the Oak Application.
  auto stub = Translator::NewStub(oak::ApplicationClient::CreateChannel(address));

  translate(stub.get(), "WORLDS", "en", "fr");
  translate(stub.get(), "WORLDS", "en", "it");
  translate(stub.get(), "WORLDS", "en", "cn");
  translate(stub.get(), "OSSIFRAGE", "en", "fr");

  return EXIT_SUCCESS;
}
