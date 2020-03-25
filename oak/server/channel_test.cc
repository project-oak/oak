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

static std::unique_ptr<Message> CreateMessage(int base) {
  auto result = absl::make_unique<Message>();
  result->data.push_back(static_cast<char>(base + 1));
  result->data.push_back(static_cast<char>(base + 2));
  result->data.push_back(static_cast<char>(base + 3));
  return result;
}

TEST(MessageChannel, BasicOperation) {
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  std::unique_ptr<MessageChannelReadHalf> read_half(std::move(halves.read));
  std::unique_ptr<MessageChannelWriteHalf> write_half(std::move(halves.write));
  ASSERT_EQ(false, read_half->CanRead());

  std::unique_ptr<Message> msg1 = CreateMessage(0x00);
  write_half->Write(std::move(msg1));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result1 = read_half->Read(1, 0);  // too small
  ASSERT_EQ(OakStatus::ERR_BUFFER_TOO_SMALL, result1.status);
  ASSERT_EQ(3, result1.required_size);
  ASSERT_EQ(nullptr, result1.msg);

  ReadResult result2 = read_half->Read(3, 0);  // just right
  ASSERT_EQ(OakStatus::OK, result2.status);
  EXPECT_NE(result2.msg, nullptr);
  ASSERT_EQ(3, result2.msg->data.size());
  ASSERT_EQ(0x01, (result2.msg->data)[0]);

  ASSERT_EQ(false, read_half->CanRead());

  ReadResult result3 = read_half->Read(10000, 0);
  ASSERT_EQ(OakStatus::OK, result3.status);
  ASSERT_EQ(nullptr, result3.msg);
  ASSERT_EQ(0, result3.required_size);

  std::unique_ptr<Message> msg2 = CreateMessage(0x10);
  write_half->Write(std::move(msg2));
  std::unique_ptr<Message> msg3 = CreateMessage(0x20);
  write_half->Write(std::move(msg3));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result4 = read_half->Read(3000, 0);
  ASSERT_EQ(OakStatus::OK, result4.status);
  EXPECT_NE(result4.msg, nullptr);
  ASSERT_EQ(3, result4.msg->data.size());
  ASSERT_EQ(0x11, (result4.msg->data)[0]);

  ReadResult result5 = read_half->Read(0, 0);
  ASSERT_EQ(OakStatus::ERR_BUFFER_TOO_SMALL, result5.status);
  ASSERT_EQ(3, result5.required_size);
  ASSERT_EQ(nullptr, result5.msg);

  ReadResult result6 = read_half->Read(10, 0);
  ASSERT_EQ(OakStatus::OK, result6.status);
  EXPECT_NE(result6.msg, nullptr);
  ASSERT_EQ(3, result6.msg->data.size());
  ASSERT_EQ(0x21, (result6.msg->data)[0]);

  ASSERT_EQ(false, read_half->CanRead());
}

TEST(MessageChannel, ChannelTransfer) {
  MessageChannel::ChannelHalves halves = MessageChannel::Create();
  std::unique_ptr<MessageChannelReadHalf> read_half(std::move(halves.read));
  std::unique_ptr<MessageChannelWriteHalf> write_half(std::move(halves.write));
  ASSERT_EQ(false, read_half->CanRead());

  std::unique_ptr<Message> msg1 = CreateMessage(0x00);
  msg1->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  write_half->Write(std::move(msg1));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result1 = read_half->Read(1000, 0);  // no space for channels
  ASSERT_EQ(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL, result1.status);
  ASSERT_EQ(3, result1.required_size);
  ASSERT_EQ(1, result1.required_channels);
  ASSERT_EQ(nullptr, result1.msg);

  ReadResult result2 = read_half->Read(1000, 1);  // just right
  ASSERT_EQ(OakStatus::OK, result2.status);
  EXPECT_NE(result2.msg, nullptr);
  ASSERT_EQ(3, result2.msg->data.size());
  ASSERT_EQ(0x01, (result2.msg->data)[0]);
  ASSERT_EQ(1, result2.msg->channels.size());

  ASSERT_EQ(false, read_half->CanRead());

  ReadResult result3 = read_half->Read(10000, 10);
  ASSERT_EQ(OakStatus::OK, result3.status);
  ASSERT_EQ(nullptr, result3.msg);
  ASSERT_EQ(0, result3.required_size);
  ASSERT_EQ(0, result3.required_channels);

  std::unique_ptr<Message> msg2 = CreateMessage(0x10);
  msg2->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  msg2->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  write_half->Write(std::move(msg2));
  std::unique_ptr<Message> msg3 = CreateMessage(0x20);
  msg3->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  msg3->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  msg3->channels.push_back(absl::make_unique<ChannelHalf>(write_half->Clone()));
  write_half->Write(std::move(msg3));

  ASSERT_EQ(true, read_half->CanRead());

  ReadResult result4 = read_half->Read(3000, 10);
  ASSERT_EQ(OakStatus::OK, result4.status);
  EXPECT_NE(result4.msg, nullptr);
  ASSERT_EQ(3, result4.msg->data.size());
  ASSERT_EQ(0x11, (result4.msg->data)[0]);
  ASSERT_EQ(2, result4.msg->channels.size());

  ReadResult result5 = read_half->Read(100, 0);
  ASSERT_EQ(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL, result5.status);
  ASSERT_EQ(3, result5.required_size);
  ASSERT_EQ(3, result5.required_channels);
  ASSERT_EQ(nullptr, result5.msg);

  ReadResult result6 = read_half->Read(10, 10);
  ASSERT_EQ(OakStatus::OK, result6.status);
  EXPECT_NE(result6.msg, nullptr);
  ASSERT_EQ(3, result6.msg->data.size());
  ASSERT_EQ(0x21, (result6.msg->data)[0]);
  ASSERT_EQ(3, result6.msg->channels.size());

  ASSERT_EQ(false, read_half->CanRead());
}

}  // namespace oak
