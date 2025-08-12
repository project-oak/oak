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

#include "cc/ffi/error_bindings.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace oak::ffi {

namespace {

using ::testing::Eq;
using ::testing::HasSubstr;

extern "C" {
bindings::Error* anyhow_error_with_three_contexts();
}

TEST(ErrorBindings, IncludesAnyhowContext) {
  bindings::Error* error = anyhow_error_with_three_contexts();
  absl::Status status = ErrorIntoStatus(error);
  EXPECT_THAT(status.message(), HasSubstr("Main error"));
  EXPECT_THAT(status.message(), HasSubstr("first context"));
  EXPECT_THAT(status.message(), HasSubstr("second context"));
  EXPECT_THAT(status.message(), HasSubstr("third context"));
}

}  // namespace

}  // namespace oak::ffi
