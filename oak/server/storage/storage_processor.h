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

#ifndef OAK_SERVER_STORAGE_PROCESSOR_H_
#define OAK_SERVER_STORAGE_PROCESSOR_H_

#include <memory>

#include "absl/status/status.h"
#include "oak/proto/storage.grpc.pb.h"
#include "third_party/asylo/statusor.h"

namespace oak {

class StorageProcessor {
 public:
  explicit StorageProcessor(const std::string& storage_address);

  // Returns item value on success.
  oak::StatusOr<std::string> Read(const std::string& storage_name, const std::string& item_name,
                                  const std::string& transaction_id);

  absl::Status Write(const std::string& storage_name, const std::string& item_name,
                     const std::string& item_value, const std::string& transaction_id);

  absl::Status Delete(const std::string& storage_name, const std::string& item_name,
                      const std::string& transaction_id);

  // Returns transaction ID on success.
  oak::StatusOr<std::string> Begin(const std::string& storage_name);

  absl::Status Commit(const std::string& storage_name, const std::string& transaction_id);

  absl::Status Rollback(const std::string& storage_name, const std::string& transaction_id);

 private:
  enum class ItemType : int { NAME, VALUE };

  // Encrypts `item` as either the name or value of a name-value pair.
  // Item names are encrypted with item_name_cryptor_, using a fixed nonce for
  // deterministic mapping of the name-value pair.
  // Item values are encrypted with item_value_cryptor_, using a random nonce.
  // Returns the concatenation of the kAesGcmSivNonceSize-byte nonce followed by
  // the encrypted item.
  const oak::StatusOr<std::string> EncryptItem(const std::string& item, ItemType item_type);

  // Decrypts `input` which must be a kAesGcmSivNonceSize-byte nonce followed by
  // the encrypted item.
  const oak::StatusOr<std::string> DecryptItem(const std::string& input, ItemType item_type);

  std::unique_ptr<oak::Storage::Stub> storage_service_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_NODE_H_
