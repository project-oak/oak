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

#ifndef OAK_COMMON_NONCE_GENERATOR_H
#define OAK_COMMON_NONCE_GENERATOR_H

#include <array>
#include <random>

#include "absl/strings/escaping.h"

namespace oak {

template <size_t N>
using Nonce = std::array<uint8_t, N>;

// NonceGenerator generates cryptographically secure nonces of the specified size.
template <size_t N>
class NonceGenerator {
 public:
  NonceGenerator() {}

  Nonce<N> NextNonce() {
    Nonce<N> nonce;
    std::uniform_int_distribution<uint8_t> distribution;
    for (uint32_t i = 0; i < nonce.size(); i++) {
      nonce[i] = distribution(prng_engine_);
    }
    return nonce;
  }

 private:
  std::random_device prng_engine_;
};

// Converts the given nonce to its binary string representation.
template <size_t N>
std::string NonceToBytes(const Nonce<N>& nonce) {
  return std::string(reinterpret_cast<const char*>(nonce.data()), nonce.size());
}

}  // namespace oak

#endif  // OAK_COMMON_NONCE_GENERATOR_H_
