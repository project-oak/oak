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

#ifndef OAK_SERVER_STORAGE_MEMORY_PROVIDER_H_
#define OAK_SERVER_STORAGE_MEMORY_PROVIDER_H_

#include <map>
#include <string>

#include "storage_provider.h"

namespace oak {

// MemoryProvider is an in-memory implementation of StorageProvider, for testing.
class MemoryProvider final : public StorageProvider {
 public:
  explicit MemoryProvider(){};

  grpc::Status Read(const StorageReadRequest* req, StorageReadResponse* rsp) override;
  grpc::Status Write(const StorageWriteRequest* req, StorageWriteResponse* rsp) override;
  grpc::Status Delete(const StorageDeleteRequest* req, StorageDeleteResponse* rsp) override;
  grpc::Status Begin(const StorageBeginRequest* req, StorageBeginResponse* rsp) override;
  grpc::Status Commit(const StorageCommitRequest* req, StorageCommitResponse* rsp) override;
  grpc::Status Rollback(const StorageRollbackRequest* req, StorageRollbackResponse* rsp) override;

 private:
  using KVStorage = std::map<std::string, std::string>;
  // Map storage_id to an in-memory KV store.
  std::map<std::string, KVStorage> stores_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_MEMORY_PROVIDER_H_
