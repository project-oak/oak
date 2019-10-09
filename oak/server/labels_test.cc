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

#include "oak/server/labels.h"

#include "gtest/gtest.h"

TEST(OakLabels, Combine) {
  oak::OakLabels got = {{"A", "B", "C"}, {"W", "X", "Y"}};
  oak::OakLabels other = {{"B", "C", "D"}, {"X", "Y", "Z"}};

  got.Merge(other);
  oak::OakLabels want = {{"A", "B", "C", "D"}, {"X", "Y"}};
  EXPECT_EQ(got.secrecy_tags, want.secrecy_tags);
  EXPECT_EQ(got.integrity_tags, want.integrity_tags);
}
