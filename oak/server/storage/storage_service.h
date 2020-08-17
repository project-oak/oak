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

#ifndef OAK_SERVER_STORAGE_STORAGE_SERVICE_H_
#define OAK_SERVER_STORAGE_STORAGE_SERVICE_H_

#include "oak_services/proto/storage.grpc.pb.h"
#include "storage_provider.h"

namespace oak {

// StorageService processes gRPC Storage::Service requests and proxies them to a
// StorageProvider implementation.
class StorageService final : public Storage::Service {
 public:
  // Takes ownership of storage_provider.
  explicit StorageService(StorageProvider* storage_provider);

  grpc::Status Read(grpc::ServerContext* context, const StorageReadRequest* request,
                    StorageReadResponse* response) override;

  grpc::Status Write(grpc::ServerContext* context, const StorageWriteRequest* request,
                     StorageWriteResponse* response) override;

  grpc::Status Delete(grpc::ServerContext* context, const StorageDeleteRequest* request,
                      StorageDeleteResponse* response) override;

  grpc::Status Begin(grpc::ServerContext* context, const StorageBeginRequest* request,
                     StorageBeginResponse* response) override;

  grpc::Status Commit(grpc::ServerContext* context, const StorageCommitRequest* request,
                      StorageCommitResponse* response) override;

  grpc::Status Rollback(grpc::ServerContext* context, const StorageRollbackRequest* request,
                        StorageRollbackResponse* response) override;

 private:
  std::unique_ptr<StorageProvider> storage_provider_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_STORAGE_SERVICE_H_
