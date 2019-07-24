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
  ReadResult result = half.Read(100000);
  ASSERT_EQ(0, result.required_size);
  ASSERT_EQ(nullptr, result.data);
}

TEST(ChannelHalf, NoWriteFallback) {
  ChannelHalf half;
  std::unique_ptr<Message> data = absl::WrapUnique(new Message{0x01, 0x02, 0x03});
  half.Write(std::move(data));
}

TEST(MessageChannel, BasicOperation) {
  MessageChannel channel;
  ASSERT_EQ(0, channel.Count());

  std::unique_ptr<Message> msg1 = absl::WrapUnique(new Message{0x01, 0x02, 0x03});
  channel.Write(std::move(msg1));

  ASSERT_EQ(1, channel.Count());

  channel.Write(nullptr);
  ASSERT_EQ(1, channel.Count());

  ReadResult result1 = channel.Read(1);  // too small
  ASSERT_EQ(3, result1.required_size);
  ASSERT_EQ(nullptr, result1.data);

  ReadResult result2 = channel.Read(3);  // just right
  EXPECT_NE(result2.data, nullptr);
  ASSERT_EQ(3, result2.data->size());
  ASSERT_EQ(0x01, (*result2.data)[0]);

  ASSERT_EQ(0, channel.Count());

  ReadResult result3 = channel.Read(10000);
  ASSERT_EQ(nullptr, result3.data);
  ASSERT_EQ(0, result3.required_size);

  std::unique_ptr<Message> msg2 = absl::WrapUnique(new Message{0x11, 0x12, 0x13});
  channel.Write(std::move(msg2));
  std::unique_ptr<Message> msg3 = absl::WrapUnique(new Message{0x21, 0x22, 0x23});
  channel.Write(std::move(msg3));

  ASSERT_EQ(2, channel.Count());

  ReadResult result4 = channel.Read(3000);
  EXPECT_NE(result4.data, nullptr);
  ASSERT_EQ(3, result4.data->size());
  ASSERT_EQ(0x11, (*result4.data)[0]);

  ReadResult result5 = channel.Read(0);
  ASSERT_EQ(3, result5.required_size);
  ASSERT_EQ(nullptr, result5.data);

  ReadResult result6 = channel.Read(10);
  EXPECT_NE(result6.data, nullptr);
  ASSERT_EQ(3, result6.data->size());
  ASSERT_EQ(0x21, (*result6.data)[0]);
}

}  // namespace oak
