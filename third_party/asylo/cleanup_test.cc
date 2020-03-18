/*
 *
 * Copyright 2018 Asylo authors
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
 *
 */

#include "asylo/util/cleanup.h"

#include <functional>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

namespace asylo {
namespace {

TEST(CleanupTest, EmptyCleanupDoesNotThrowExceptions) { Cleanup do_nothing; }

TEST(CleanupTest, DestructorCallsCleanupFunction) {
  int counter = 0;

  {
    Cleanup increment_counter([&counter]() { ++counter; });
    EXPECT_EQ(counter, 0);
  }

  EXPECT_EQ(counter, 1);
}

TEST(CleanupTest, ReleasePreventsDestructorCleanupFunctionCall) {
  int counter = 0;
  std::function<void()> cleanup_holder;

  {
    Cleanup increment_counter([&counter]() { ++counter; });
    EXPECT_EQ(counter, 0);

    cleanup_holder = increment_counter.release();
  }

  EXPECT_EQ(counter, 0);

  cleanup_holder();
  EXPECT_EQ(counter, 1);
}

}  // namespace
}  // namespace asylo
