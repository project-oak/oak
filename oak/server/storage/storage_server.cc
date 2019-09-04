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
#include "absl/strings/str_cat.h"
#include "asylo/util/logging.h"
#include "grpc/grpc.h"
#include "grpcpp/channel.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/security/server_credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "oak/server/storage/memory_provider.h"
//#include "spanner_provider.h"
#include "storage_service.h"

ABSL_FLAG(std::string, port, "7867", "Port on which the Storage Server listens.");

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  LOG(INFO) << "Creating service";
  //  oak::StorageService storage_service(new oak::SpannerProvider(
  //      grpc::CreateChannel("localhost:9999", grpc::InsecureChannelCredentials())));
  oak::StorageService storage_service(new oak::MemoryProvider());

  std::string server_address = absl::StrCat("[::]:", absl::GetFlag(FLAGS_port));
  std::shared_ptr<grpc::ServerCredentials> credentials = grpc::InsecureServerCredentials();

  LOG(INFO) << "Creating server";
  grpc::ServerBuilder builder;
  builder.AddListeningPort(server_address, credentials);
  builder.RegisterService(&storage_service);

  LOG(INFO) << "Starting gRPC Storage Server";
  std::unique_ptr<grpc::Server> server(builder.BuildAndStart());
  server->Wait();

  return 0;
}
