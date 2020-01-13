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

#include "oak/server/time/roughtime_util.h"

#include "gtest/gtest.h"

namespace oak {

TEST(RoughtimeUtil, TestValidOverlapOneOfThree) {
  std::vector<RoughtimeInterval> intervals{{1, 4}, {2, 6}, {3, 5}};
  auto interval_or_status = FindOverlap(intervals, 1);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 1);
  ASSERT_EQ(interval.max, 4);
}

TEST(RoughtimeUtil, TestValidOverlapTwoOfThree) {
  std::vector<RoughtimeInterval> intervals{{1, 4}, {2, 6}, {3, 5}};
  auto interval_or_status = FindOverlap(intervals, 2);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 2);
  ASSERT_EQ(interval.max, 4);
}

TEST(RoughtimeUtil, TestValidOverlapThreeOfThree) {
  std::vector<RoughtimeInterval> intervals{{1, 4}, {2, 6}, {3, 5}};
  auto interval_or_status = FindOverlap(intervals, 3);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 3);
  ASSERT_EQ(interval.max, 4);
}

TEST(RoughtimeUtil, TestValidOverlapOneOfThreeReversed) {
  std::vector<RoughtimeInterval> intervals{{3, 5}, {2, 6}, {1, 4}};
  auto interval_or_status = FindOverlap(intervals, 1);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 3);
  ASSERT_EQ(interval.max, 5);
}

TEST(RoughtimeUtil, TestValidOverlapTwoOfThreeReversed) {
  std::vector<RoughtimeInterval> intervals{{3, 5}, {2, 6}, {1, 4}};
  auto interval_or_status = FindOverlap(intervals, 2);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 3);
  ASSERT_EQ(interval.max, 5);
}

TEST(RoughtimeUtil, TestValidOverlapThreeOfThreeReversed) {
  std::vector<RoughtimeInterval> intervals{{3, 5}, {2, 6}, {1, 4}};
  auto interval_or_status = FindOverlap(intervals, 3);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 3);
  ASSERT_EQ(interval.max, 4);
}

TEST(RoughtimeUtil, TestValidOverlapFiveOfTen) {
  std::vector<RoughtimeInterval> intervals{{1, 2}, {1, 9}, {2, 9}, {3, 9}, {4, 9},
                                           {5, 9}, {6, 9}, {7, 9}, {8, 9}, {9, 9}};
  auto interval_or_status = FindOverlap(intervals, 5);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 5);
  ASSERT_EQ(interval.max, 9);
}

TEST(RoughtimeUtil, TestValidOverlapPoint) {
  std::vector<RoughtimeInterval> intervals{{4, 8}, {1, 4}};
  auto interval_or_status = FindOverlap(intervals, 2);
  ASSERT_TRUE(interval_or_status.ok());
  auto interval = interval_or_status.ValueOrDie();
  ASSERT_EQ(interval.min, 4);
  ASSERT_EQ(interval.max, 4);
}

TEST(RoughtimeUtil, TestInvalidOverlapFourOfThree) {
  std::vector<RoughtimeInterval> intervals{{1, 4}, {2, 6}, {3, 5}};
  auto interval_or_status = FindOverlap(intervals, 4);
  ASSERT_FALSE(interval_or_status.ok());
}

TEST(RoughtimeUtil, TestInvalidOverlapThreeOfThree) {
  std::vector<RoughtimeInterval> intervals{{1, 2}, {3, 6}, {3, 5}};
  auto interval_or_status = FindOverlap(intervals, 3);
  ASSERT_FALSE(interval_or_status.ok());
}

TEST(RoughtimeUtil, TestInvalidOverlapInvertedIntervals) {
  std::vector<RoughtimeInterval> intervals{{4, 1}, {6, 2}, {5, 3}};
  auto interval_or_status = FindOverlap(intervals, 3);
  ASSERT_FALSE(interval_or_status.ok());
}

}  // namespace oak
