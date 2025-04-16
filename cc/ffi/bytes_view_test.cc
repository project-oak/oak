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

#include "cc/ffi/bytes_view.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::ffi {
namespace {

using ::testing::Eq;

absl::string_view AcceptsStringView(absl::string_view sv) { return sv; }

TEST(BytesViewTest, BytesViewCoercesToStringView) {
  std::string str = "Some string";
  bindings::BytesView bytes_view(str);

  EXPECT_THAT(AcceptsStringView(bytes_view), Eq(str));
}  // namespace
}  // namespace
}  // namespace oak::ffi
