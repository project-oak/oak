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

#ifndef OAK_COMMON_HMAC_H_
#define OAK_COMMON_HMAC_H_

#include "asylo/util/statusor.h"

using asylo::StatusOr;

namespace oak {
namespace utils {

// Computes a HMAC-SHA256 with the provided key over the provided message.
//
// See https://en.wikipedia.org/wiki/HMAC.
StatusOr<std::string> hmac_sha256(const std::string& key, const std::string& message);

}  // namespace utils
}  // namespace oak

#endif  // OAK_COMMON_HMAC_H_
