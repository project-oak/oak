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

#include "memory_provider.h"

#include "absl/strings/str_cat.h"

namespace oak {

grpc::Status MemoryProvider::Read(const StorageReadRequest* req, StorageReadResponse* rsp) {
  auto store = stores_.find(req->storage_id());
  if (store == stores_.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No store found for storage ID ", req->storage_id()));
  }
  auto kv = store->second.find(req->datum_name());
  if (kv == store->second.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No value found for ", req->datum_name()));
  }
  rsp->set_datum_value(kv->second);

  return grpc::Status::OK;
}

grpc::Status MemoryProvider::Write(const StorageWriteRequest* req, StorageWriteResponse*) {
  stores_[req->storage_id()][req->datum_name()] = req->datum_value();
  return grpc::Status::OK;
}

grpc::Status MemoryProvider::Delete(const StorageDeleteRequest* req, StorageDeleteResponse*) {
  auto store = stores_.find(req->storage_id());
  if (store == stores_.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No store found for storage ID ", req->storage_id()));
  }
  store->second.erase(req->datum_name());
  return grpc::Status::OK;
}

grpc::Status MemoryProvider::Begin(const StorageBeginRequest*, StorageBeginResponse*) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "No transaction semantics here");
}
grpc::Status MemoryProvider::Commit(const StorageCommitRequest*, StorageCommitResponse*) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "No transaction semantics here");
}
grpc::Status MemoryProvider::Rollback(const StorageRollbackRequest*, StorageRollbackResponse*) {
  return grpc::Status(grpc::StatusCode::UNIMPLEMENTED, "No transaction semantics here");
}

}  // namespace oak
