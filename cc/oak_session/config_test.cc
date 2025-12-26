/*
 * Copyright 2024 The Project Oak Authors
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

#include "cc/oak_session/config.h"

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "gtest/gtest.h"

namespace oak::session {
namespace {

TEST(SessionConfigBuilderTest, UpdateRawFailure) {
  SessionConfigBuilder builder(AttestationType::kUnattested,
                               HandshakeType::kNoiseNN);
  absl::Status updated_status =
      builder.UpdateRaw([](SessionConfigBuilderHolder bytes)
                            -> absl::StatusOr<SessionConfigBuilderHolder> {
        return absl::InvalidArgumentError("Something went wrong");
      });
  EXPECT_EQ(updated_status.code(), absl::StatusCode::kInvalidArgument);
}

TEST(SessionConfigBuilderTest, UpdateRawSuccess) {
  SessionConfigBuilder builder(AttestationType::kUnattested,
                               HandshakeType::kNoiseNN);
  absl::Status updated_status =
      builder.UpdateRaw([](SessionConfigBuilderHolder ptr)
                            -> absl::StatusOr<SessionConfigBuilderHolder> {
        return std::move(ptr);
      });
  EXPECT_TRUE(updated_status.ok());
}

}  // namespace
}  // namespace oak::session
