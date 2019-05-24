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

#ifndef OAK_SERVER_STORAGE_SPANNER_PROVIDER_H_
#define OAK_SERVER_STORAGE_SPANNER_PROVIDER_H_

#include "google/spanner/v1/spanner.grpc.pb.h"
#include "storage_provider.h"

namespace oak {

// SpannerProvider is an implementation of StorageProvider using Cloud Spanner.
class SpannerProvider final : public StorageProvider {
 public:
  explicit SpannerProvider(std::shared_ptr<grpc::ChannelInterface> channel);

  grpc::Status Read(const ReadRequest* request, ReadResponse* response) override;
  grpc::Status Write(const WriteRequest* request, WriteResponse* response) override;
  grpc::Status Delete(const DeleteRequest* request, DeleteResponse* response) override;
  grpc::Status Begin(const BeginRequest* request, BeginResponse* response) override;
  grpc::Status Commit(const CommitRequest* request, CommitResponse* response) override;
  grpc::Status Rollback(const RollbackRequest* request, RollbackResponse* response) override;

 private:
  std::unique_ptr<google::spanner::v1::Spanner::Stub> spanner_service_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_SPANNER_PROVIDER_H_
