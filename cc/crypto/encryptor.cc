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

#include "encryptor.h"

#include "absl/status/statusor.h"
#include "hpke.h"

namespace oak::crypto {

absl::StatusOr<std::unique_ptr<ClientEncryptor>> ClientEncryptor::Create(
    absl::string_view serialized_server_public_key) {
  absl::StatusOr<ClientHPKEConfig> client_setup =
      SetUpBaseSender(serialized_server_public_key, OAK_HPKE_INFO);
  if (!client_setup.ok()) {
    return client_setup.status();
  }
  auto client_encryptor = std::unique_ptr<ClientEncryptor>(new ClientEncryptor(*client_setup));
  return client_encryptor;
}

}  // namespace oak::crypto
