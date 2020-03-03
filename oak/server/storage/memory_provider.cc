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

#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "asylo/util/logging.h"

namespace oak {

grpc::Status MemoryProvider::Read(const StorageReadRequest* req, StorageReadResponse* rsp) {
  auto store = stores_.find(req->storage_id());
  if (store == stores_.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No store found for storage ID ", req->storage_id()));
  }
  auto kv = store->second.find(req->item_name());
  if (kv == store->second.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No value found for ", req->item_name()));
  }
  LOG(INFO) << "READ   store[" << req->storage_id() << "]: ["
            << absl::BytesToHexString(req->item_name())
            << "] = " << absl::BytesToHexString(kv->second);
  rsp->set_item_value(kv->second);

  return grpc::Status::OK;
}

grpc::Status MemoryProvider::Write(const StorageWriteRequest* req, StorageWriteResponse*) {
  LOG(INFO) << "WRITE  store[" << req->storage_id() << "]: ["
            << absl::BytesToHexString(req->item_name())
            << "] = " << absl::BytesToHexString(req->item_value());
  stores_[req->storage_id()][req->item_name()] = req->item_value();
  return grpc::Status::OK;
}

grpc::Status MemoryProvider::Delete(const StorageDeleteRequest* req, StorageDeleteResponse*) {
  auto store = stores_.find(req->storage_id());
  if (store == stores_.end()) {
    return grpc::Status(grpc::StatusCode::NOT_FOUND,
                        absl::StrCat("No store found for storage ID ", req->storage_id()));
  }
  LOG(INFO) << "DELETE store[" << req->storage_id() << "]: ["
            << absl::BytesToHexString(req->item_name()) << "]";
  store->second.erase(req->item_name());
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
