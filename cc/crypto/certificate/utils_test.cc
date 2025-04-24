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

#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "google/protobuf/timestamp.pb.h"
#include "gtest/gtest.h"

constexpr uint64_t kTestTimeSeconds = 12;
constexpr uint64_t kTestTimeNanoseconds = 3456;

namespace oak::crypto {
namespace {

using google::protobuf::Timestamp;

TEST(UtilsTest, ToTimestampSucceeds) {
  absl::Time time = absl::FromUnixSeconds(kTestTimeSeconds) +
                    absl::Nanoseconds(kTestTimeNanoseconds);

  absl::StatusOr<Timestamp> timestamp = ToTimestamp(time);
  ASSERT_TRUE(timestamp.ok());
  EXPECT_EQ(timestamp->seconds(), kTestTimeSeconds);
  EXPECT_EQ(timestamp->nanos(), kTestTimeNanoseconds);

  auto parsed_time = FromTimestamp(*timestamp);
  EXPECT_EQ(parsed_time, time);
}

TEST(UtilsTest, ToTimestampFails) {
  // TODO: b/414973369 - Use `TimeUtil::kTimestampMinSeconds` and
  // `TimeUtil::kTimestampMaxSeconds` once go/oak-cr/19460 is submitted.
  absl::Time time_under_limit = absl::FromUnixSeconds(kTimestampMinSeconds - 1);
  absl::Time time_over_limit = absl::FromUnixSeconds(kTimestampMaxSeconds + 1);

  absl::StatusOr<Timestamp> result_under_limit = ToTimestamp(time_under_limit);
  EXPECT_FALSE(result_under_limit.ok());
  absl::StatusOr<Timestamp> result_over_limit = ToTimestamp(time_over_limit);
  EXPECT_FALSE(result_over_limit.ok());
}

}  // namespace
}  // namespace oak::crypto
