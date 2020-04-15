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

#include "oak/server/time/roughtime_client.h"

#include <chrono>

#include "gtest/gtest.h"
#include "oak/common/logging.h"

namespace oak {

// Tests getting the live Roughtime from the hardcoded servers.
// This requires an internet connection and both the Roughtime servers to be up.
TEST(RoughtimeClient, TestGetRoughTimeLive) {
  auto current = std::chrono::duration_cast<std::chrono::microseconds>(
                     std::chrono::system_clock::now().time_since_epoch())
                     .count();
  RoughtimeClient client;
  auto time_or_status = client.GetRoughTime();
  ASSERT_TRUE(time_or_status.ok());
  auto time = time_or_status.ValueOrDie();

  OAK_LOG(INFO) << "System time: " << current << "μs from the epoch.";
  OAK_LOG(INFO) << "Roughtime: " << time << "μs from the epoch.";
  OAK_LOG(INFO) << "Difference: " << time - current << "μs.";

  ASSERT_LE(current - 60000000, time);
  ASSERT_GE(current + 60000000, time);
}

}  // namespace oak
