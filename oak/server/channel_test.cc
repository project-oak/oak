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

#include <thread>

#include "absl/memory/memory.h"
#include "gtest/gtest.h"

namespace oak {

TEST(MessageChannel, BasicOperation) {
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  std::unique_ptr<MessageChannelReadHalf> read_half(std::move(halves.read));
  std::unique_ptr<MessageChannelWriteHalf> write_half(std::move(halves.write));
  ASSERT_EQ(false, read_half->CanRead());

  std::unique_ptr<Message> msg1 = absl::WrapUnique(new Message{0x01, 0x02, 0x03});
  write_half->Write(std::move(msg1));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result1 = read_half->Read(1);  // too small
  ASSERT_EQ(3, result1.required_size);
  ASSERT_EQ(nullptr, result1.data);

  ReadResult result2 = read_half->Read(3);  // just right
  EXPECT_NE(result2.data, nullptr);
  ASSERT_EQ(3, result2.data->size());
  ASSERT_EQ(0x01, (*result2.data)[0]);

  ASSERT_EQ(false, read_half->CanRead());

  ReadResult result3 = read_half->Read(10000);
  ASSERT_EQ(nullptr, result3.data);
  ASSERT_EQ(0, result3.required_size);

  std::unique_ptr<Message> msg2 = absl::WrapUnique(new Message{0x11, 0x12, 0x13});
  write_half->Write(std::move(msg2));
  std::unique_ptr<Message> msg3 = absl::WrapUnique(new Message{0x21, 0x22, 0x23});
  write_half->Write(std::move(msg3));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result4 = read_half->Read(3000);
  EXPECT_NE(result4.data, nullptr);
  ASSERT_EQ(3, result4.data->size());
  ASSERT_EQ(0x11, (*result4.data)[0]);

  ReadResult result5 = read_half->Read(0);
  ASSERT_EQ(3, result5.required_size);
  ASSERT_EQ(nullptr, result5.data);

  ReadResult result6 = read_half->Read(10);
  EXPECT_NE(result6.data, nullptr);
  ASSERT_EQ(3, result6.data->size());
  ASSERT_EQ(0x21, (*result6.data)[0]);
}

}  // namespace oak
