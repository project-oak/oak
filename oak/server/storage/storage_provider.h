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

#include "oak/proto/storage.grpc.pb.h"

namespace oak {

// StorageProvider is an abstract interface for implementations of a
// persistent data store for StorageService.  This is an opaque name-value
// store that should handle only encrypted blobs of data.
class StorageProvider {
 public:
  StorageProvider() {}

  virtual grpc::Status Read(const ReadRequest* request, ReadResponse* response) = 0;
  virtual grpc::Status Write(const WriteRequest* request, WriteResponse* response) = 0;
  virtual grpc::Status Delete(const DeleteRequest* request, DeleteResponse* response) = 0;
  virtual grpc::Status Begin(const BeginRequest* request, BeginResponse* response) = 0;
  virtual grpc::Status Commit(const CommitRequest* request, CommitResponse* response) = 0;
  virtual grpc::Status Rollback(const RollbackRequest* request, RollbackResponse* response) = 0;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_STORAGE_PROVIDER_H_
