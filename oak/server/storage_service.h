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

#ifndef OAK_SERVER_STORAGE_SERVICE_H_
#define OAK_SERVER_STORAGE_SERVICE_H_

#include "google/spanner/v1/spanner.grpc.pb.h"
#include "oak/proto/storage.grpc.pb.h"

namespace oak {

class StorageService final : public Storage::Service {
 public:
  StorageService(std::shared_ptr<grpc::ChannelInterface> channel);

  grpc::Status Read(grpc::ServerContext* context, const ReadRequest* request,
                    ReadResponse* response) override;

  grpc::Status Write(grpc::ServerContext* context, const WriteRequest* request,
                     WriteResponse* response) override;

  grpc::Status Delete(grpc::ServerContext* context, const DeleteRequest* request,
                      DeleteResponse* response) override;

  grpc::Status Begin(grpc::ServerContext* context, const BeginRequest* request,
                     BeginResponse* response) override;

  grpc::Status Commit(grpc::ServerContext* context, const CommitRequest* request,
                      CommitResponse* response) override;

  grpc::Status Rollback(grpc::ServerContext* context, const RollbackRequest* request,
                        RollbackResponse* response) override;

 private:
  std::unique_ptr<google::spanner::v1::Spanner::Stub> spanner_service_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_SERVICE_H_
