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

#ifndef CC_TRANSPORT_TRANSPORT_H_
#define CC_TRANSPORT_TRANSPORT_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace oak::transport {

// Abstract class for sending messages to the enclave.
class Transport {
 public:
  virtual ~Transport() = default;

  // Sends a request to the enclave and returns a response.
  virtual absl::StatusOr<std::string> Invoke(absl::string_view request_bytes) = 0;
};

}  // namespace oak::transport

#endif  // CC_TRANSPORT_TRANSPORT_H_
