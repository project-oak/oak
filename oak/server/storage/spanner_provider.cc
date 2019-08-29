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

#include "spanner_provider.h"

namespace oak {

using google::spanner::v1::Spanner;

SpannerProvider::SpannerProvider(std::shared_ptr<grpc::ChannelInterface> channel)
    : spanner_service_(Spanner::NewStub(channel)) {}

grpc::Status SpannerProvider::Read(const StorageReadRequest* request,
                                   StorageReadResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "Read method not implemented.");
}
grpc::Status SpannerProvider::Write(const StorageWriteRequest* request,
                                    StorageWriteResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "Write method not implemented.");
}
grpc::Status SpannerProvider::Delete(const StorageDeleteRequest* request,
                                     StorageDeleteResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}
grpc::Status SpannerProvider::Begin(const StorageBeginRequest* request,
                                    StorageBeginResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}
grpc::Status SpannerProvider::Commit(const StorageCommitRequest* request,
                                     StorageCommitResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}
grpc::Status SpannerProvider::Rollback(const StorageRollbackRequest* request,
                                       StorageRollbackResponse* response) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "");
}

}  // namespace oak
