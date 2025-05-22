/*
 * Copyright 2025 The Project Oak Authors
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

#ifndef CC_CRYPTO_CERTIFICATE_UTILS_H_
#define CC_CRYPTO_CERTIFICATE_UTILS_H_

#include "absl/time/time.h"
#include "google/protobuf/timestamp.pb.h"

namespace oak::crypto {

class Clock {
 public:
  virtual absl::Time CurrentTime() const = 0;

  virtual ~Clock() = default;
};

class SystemClock : public Clock {
 public:
  absl::Time CurrentTime() const;
};

// Converts [`absl::Time`] point into the Timestamp proto.
absl::StatusOr<google::protobuf::Timestamp> ToTimestamp(absl::Time time);

// Converts Timestamp proto to [`absl::Time`].
absl::Time FromTimestamp(const google::protobuf::Timestamp& timestamp);

}  // namespace oak::crypto

#endif  // CC_CRYPTO_CERTIFICATE_UTILS_H_
