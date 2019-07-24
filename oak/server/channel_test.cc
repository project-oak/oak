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

#include "oak/server/channel.h"

#include "absl/memory/memory.h"
#include "gtest/gtest.h"

namespace oak {

TEST(ChannelHalf, EmptyReadFallback) {
  ChannelHalf half;
  ChannelHalf::ReadResult result = half.Read(100000);
  ASSERT_EQ(0, result.required_size);
  ASSERT_EQ(nullptr, result.data);
}

TEST(ChannelHalf, NoWriteFallback) {
  ChannelHalf half;
  std::unique_ptr<Message> data = absl::WrapUnique(new Message{0x01, 0x02, 0x03});
  half.Write(std::move(data));
}

}  // namespace oak
