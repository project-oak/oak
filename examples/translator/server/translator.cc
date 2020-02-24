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

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/strings/str_cat.h"
#include "asylo/util/logging.h"
#include "examples/translator/proto/translator.grpc.pb.h"
#include "examples/translator/proto/translator.pb.h"
#include "include/grpcpp/grpcpp.h"

ABSL_FLAG(std::string, port, "7770", "Port on which this Server listens.");

using ::oak::examples::translator::TranslateRequest;
using ::oak::examples::translator::TranslateResponse;
using ::oak::examples::translator::Translator;

// Server class for the Translator with minimal contents, intended for use in testing.
class TranslatorService final : public Translator::Service {
 public:
  explicit TranslatorService() {}

  grpc::Status Translate(grpc::ServerContext* context, const TranslateRequest* req,
                         TranslateResponse* rsp) override {
    LOG(INFO) << "attempt to translate '" << req->text() << "' from " << req->from_lang() << " to "
              << req->to_lang();
    if (req->from_lang() != "en") {
      LOG(INFO) << "input language '" << req->from_lang() << "' not recognized";
      return grpc::Status(grpc::StatusCode::NOT_FOUND, "Input language unrecognized");
    }
    if (req->text() == "WORLDS") {
      if (req->to_lang() == "fr") {
        rsp->set_translated_text("MONDES");
      } else if (req->to_lang() == "it") {
        rsp->set_translated_text("MONDI");
      } else {
        LOG(INFO) << "output language " << req->to_lang() << " not found";
        return grpc::Status(grpc::StatusCode::NOT_FOUND, "Output language not found");
      }
    } else {
      LOG(INFO) << "input text '" << req->text() << "' in " << req->from_lang()
                << " not recognized";
      return grpc::Status(grpc::StatusCode::NOT_FOUND, "Input text unrecognized");
    }
    LOG(INFO) << "translation '" << rsp->translated_text() << "'";
    return grpc::Status::OK;
  }
};

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  grpc::ServerBuilder builder;
  std::string server_address = absl::StrCat("[::]:", absl::GetFlag(FLAGS_port));
  std::shared_ptr<grpc::ServerCredentials> credentials = grpc::InsecureServerCredentials();
  builder.AddListeningPort(server_address, credentials);
  TranslatorService translator_service;
  builder.RegisterService(&translator_service);

  LOG(INFO) << "Starting gRPC Server on " << server_address;
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  server->Wait();

  return 0;
}
