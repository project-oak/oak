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

#ifndef OAK_SERVER_STORAGE_NODE_H_
#define OAK_SERVER_STORAGE_NODE_H_

#include <memory>
#include <thread>

#include "absl/strings/string_view.h"
#include "asylo/crypto/aes_gcm_siv.h"
#include "asylo/util/statusor.h"
#include "oak/common/handles.h"
#include "oak/proto/storage.grpc.pb.h"
#include "oak/server/channel.h"
#include "oak/server/node_thread.h"
#include "oak/server/storage/fixed_nonce_generator.h"

namespace oak {

class StorageNode final : public NodeThread {
 public:
  StorageNode(const std::string& name, const std::string& storage_address);

 private:
  const asylo::StatusOr<std::string> Encrypt(asylo::AesGcmSivCryptor* cryptor,
                                             const absl::string_view& data);
  const asylo::StatusOr<std::string> EncryptDatumName(const absl::string_view& datum_name);
  const asylo::StatusOr<std::string> EncryptDatumValue(const absl::string_view& datum_value);

  const asylo::StatusOr<std::string> DecryptDatumValue(const absl::string_view& datum_value);

  void Run() override;

  FixedNonceGenerator* fixed_nonce_generator_;
  asylo::AesGcmSivCryptor datum_name_cryptor_;
  asylo::AesGcmSivCryptor datum_value_cryptor_;

  std::unique_ptr<oak::Storage::Stub> storage_service_;
  std::thread storage_thread_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_NODE_H_
