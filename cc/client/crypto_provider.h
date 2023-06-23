/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_OAK_CLIENT_CRYPTO_PROVIDER_H_
#define CC_OAK_CLIENT_CRYPTO_PROVIDER_H_

#include <string>

#include "absl/status/statusor.h"

namespace oak::oak_client {

// Abstract decryptor class for deciphering encrypted messages.
class Decryptor {
 public:
  virtual ~Decryptor() = default;
  virtual absl::StatusOr<std::string> Decrypt(std::string encrypted_message) = 0;
};

// Abstract encryptor class for encrypting raw messages.
class Encryptor {
 public:
  virtual ~Encryptor() = default;
  virtual absl::StatusOr<std::string> Encrypt(std::string unencrypted_message) = 0;
};

// Abstract crypto provider class that maintains an encryptor and decryptor for
// encoding and decoding messages sent to and from the enclave.
class CryptoProvider {
 public:
  virtual ~CryptoProvider() = default;
  // Sets the class' public key used for encryption. This should be called prior
  // to calling GetEncryptor.
  virtual void SetEnclavePublicKey(std::string enclave_public_key) = 0;

  // The encryptor is based on the enclave's public key.
  virtual Encryptor* GetEncryptor() = 0;
  // The decryptor is based on the client's response key.
  virtual Decryptor* GetDecryptor() = 0;
};

}  // namespace oak::oak_client

#endif  // CC_OAK_CLIENT_CRYPTO_PROVIDER_H_