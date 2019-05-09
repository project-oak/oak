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

#include "storage_service.h"

namespace oak {

using google::spanner::v1::Spanner;

StorageService::StorageService(std::shared_ptr<grpc::ChannelInterface> channel)
    : Storage::Service(), spanner_service_(Spanner::NewStub(channel)) {}

grpc::Status StorageService::Read(grpc::ServerContext* context, const ReadRequest* request,
                                  ReadResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status StorageService::Write(grpc::ServerContext* context, const WriteRequest* request,
                                   WriteResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status StorageService::Delete(grpc::ServerContext* context, const DeleteRequest* request,
                                    DeleteResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status StorageService::Begin(grpc::ServerContext* context, const BeginRequest* request,
                                   BeginResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status StorageService::Commit(grpc::ServerContext* context, const CommitRequest* request,
                                    CommitResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

grpc::Status StorageService::Rollback(grpc::ServerContext* context, const RollbackRequest* request,
                                      RollbackResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

}  // namespace oak
