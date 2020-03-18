/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/common/hmac.h"

#include <openssl/hmac.h>
#include <openssl/sha.h>

#include "absl/status/status.h"
#include "third_party/asylo/statusor.h"

namespace oak {
namespace utils {

oak::StatusOr<std::string> hmac_sha256(const std::string& key, const std::string& message) {
  const EVP_MD* digest = EVP_sha256();
  uint8_t mac[SHA256_DIGEST_LENGTH];
  unsigned int out_size;
  if (HMAC(digest, key.data(), key.size(), reinterpret_cast<const uint8_t*>(message.data()),
           message.size(), mac, &out_size) == nullptr) {
    return absl::Status(absl::StatusCode::kInternal, "Could not compute HMAC-SHA256");
  };
  return std::string(reinterpret_cast<const char*>(mac), out_size);
}

}  // namespace utils
}  // namespace oak
