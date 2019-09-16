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
  enum class DatumType : int { NAME, VALUE };

  // Encrypts `datum` as either the name or value of a name-value pair.
  // Datum names are encrypted with datum_name_cryptor_, using a fixed nonce for
  // deterministic mapping of the name-value pair.
  // Datum values are encrypted with datum_value_cryptor_, using a random nonce.
  // Returns the concatenation of the kAesGcmSivNonceSize-byte nonce followed by
  // the encrypted datum.
  // TODO: Convert this to a serialized protocol message.
  const asylo::StatusOr<std::string> EncryptDatum(const std::string& datum, DatumType datum_type);

  // Decrypts `input` which must be a kAesGcmSivNonceSize-byte nonce followed by
  // the encrypted datum.
  const asylo::StatusOr<std::string> DecryptDatum(const std::string& input, DatumType datum_type);

  void Run() override;

  // Fixed nonce generator owned by datum_name_cryptor_.
  FixedNonceGenerator* fixed_nonce_generator_;

  // Cryptor that uses a fixed nonce for deterministic encryption of datum names.
  asylo::AesGcmSivCryptor datum_name_cryptor_;
  // Cryptor that uses a random nonce for encryption of datum values.
  asylo::AesGcmSivCryptor datum_value_cryptor_;

  std::unique_ptr<oak::Storage::Stub> storage_service_;
};

}  // namespace oak

#endif  // OAK_SERVER_STORAGE_NODE_H_
