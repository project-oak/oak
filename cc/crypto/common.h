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

#ifndef CC_CRYPTO_COMMON_H_
#define CC_CRYPTO_COMMON_H_

#include "absl/strings/string_view.h"

namespace oak::crypto {

// Info string used by Hybrid Public Key Encryption.
inline constexpr absl::string_view kOakHPKEInfo =
    "Oak Hybrid Public Key Encryption v1";

struct DecryptionResult {
  std::string plaintext;
  std::string associated_data;
};

}  // namespace oak::crypto

#endif  // CC_CRYPTO_COMMON_H_
