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

#ifndef OAK_SERVER_STORAGE_STORAGE_PROVIDER_H_
#define OAK_SERVER_STORAGE_STORAGE_PROVIDER_H_

#include "include/grpcpp/support/status.h"
#include "oak_services/proto/storage.pb.h"

namespace oak {

// StorageProvider is an abstract interface for Storage::Service implementations
// of persistent storage.  It is an opaque name-value store that should handle
// only encrypted blobs of data.
class StorageProvider {
 public:
  StorageProvider() {}
  virtual ~StorageProvider() {}

  virtual grpc::Status Read(const StorageReadRequest* request, StorageReadResponse* response) = 0;
  virtual grpc::Status Write(const StorageWriteRequest* request,
                             StorageWriteResponse* response) = 0;
  virtual grpc::Status Delete(const StorageDeleteRequest* request,
                              StorageDeleteResponse* response) = 0;
  virtual grpc::Status Begin(const StorageBeginRequest* request,
                             StorageBeginResponse* response) = 0;
  virtual grpc::Status Commit(const StorageCommitRequest* request,
                              StorageCommitResponse* response) = 0;
  virtual grpc::Status Rollback(const StorageRollbackRequest* request,
                                StorageRollbackResponse* response) = 0;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_STORAGE_PROVIDER_H_
