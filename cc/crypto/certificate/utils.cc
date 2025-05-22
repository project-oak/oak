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

#include "cc/crypto/certificate/utils.h"

#include <cstdint>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/time/time.h"
#include "google/protobuf/timestamp.pb.h"
#include "google/protobuf/util/time_util.h"

namespace oak::crypto {

namespace {
using google::protobuf::Timestamp;
using google::protobuf::util::TimeUtil;
}  // namespace

absl::Time SystemClock::CurrentTime() const { return absl::Now(); }

absl::StatusOr<Timestamp> ToTimestamp(absl::Time time) {
  absl::Time kMinTime = absl::FromUnixSeconds(TimeUtil::kTimestampMinSeconds);
  absl::Time kMaxTime = absl::FromUnixSeconds(TimeUtil::kTimestampMaxSeconds);
  if (time < kMinTime || time > kMaxTime) {
    return absl::InvalidArgumentError(absl::StrCat(
        "couldn't convert absl::Time to google::protobuf::Timestamp: ", time,
        " is not in the [", kMinTime, ", ", kMaxTime, "] interval"));
  }

  auto const seconds = absl::ToUnixSeconds(time);
  auto const nanoseconds =
      absl::ToInt64Nanoseconds(time - absl::FromUnixSeconds(seconds));
  google::protobuf::Timestamp timestamp;
  timestamp.set_seconds(seconds);
  timestamp.set_nanos(static_cast<std::int32_t>(nanoseconds));
  return timestamp;
}

absl::Time FromTimestamp(const Timestamp& timestamp) {
  return absl::FromUnixSeconds(timestamp.seconds()) +
         absl::Nanoseconds(timestamp.nanos());
}

}  // namespace oak::crypto
