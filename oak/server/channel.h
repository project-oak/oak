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

#ifndef OAK_SERVER_CHANNEL_H_
#define OAK_SERVER_CHANNEL_H_

#include <cstdint>
#include <deque>
#include <memory>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/memory/memory.h"
#include "absl/synchronization/mutex.h"
#include "absl/types/variant.h"

namespace oak {

class MessageChannelWriteHalf;  // forward declaration
class MessageChannelReadHalf;   // forward declaration

// Owning reference to either a read or write half of a channel.
using ChannelHalf = absl::variant<std::unique_ptr<MessageChannelReadHalf>,
                                  std::unique_ptr<MessageChannelWriteHalf>>;

// Each message transferred over a channel includes data and potentially
// also references to halves of channels.
struct Message {
  std::vector<char> data;
  std::vector<std::unique_ptr<ChannelHalf>> channels;
};

// Result of a read operation. If the operation would have produced a message
// bigger than the requested maximum size, then |required_size| will be non-zero
// and indicates the required size for the message.  If the operation would have
// been accompanied by more than the requested maximum channel count, then
// |required_channels| will be non-zero and indicates the required channel count
// for the message. Otherwise, |required_size| and |required_channels| will be
// zero and |data| holds the message (transferring ownership).
struct ReadResult {
  uint32_t required_size;
  uint32_t required_channels;
  std::unique_ptr<Message> msg;
};

// A channel, which holds an arbitrary number of queued messages in a
// uni-directional stream.  Users do not access MessageChannel objects directly;
// all operations are performed via either a read or write half of the channel.
//
// No flow control is implemented at this level; application
// may decide to build some of these abstractions on top of the Channel
// interface.
//
// Each channel may be connected to a built-in component, or to a local or
// (in future) remote Oak Node.
//
// TODO: add a hard limit for message size
class MessageChannel {
 public:
  struct ChannelHalves {
    std::unique_ptr<MessageChannelWriteHalf> write;
    std::unique_ptr<MessageChannelReadHalf> read;
  };

  // Create a message channel and return references to both halves of it.
  static ChannelHalves Create();

 private:
  friend class MessageChannelReadHalf;
  friend class MessageChannelWriteHalf;

  MessageChannel() {}

  // Count indicates the number of pending messages.
  size_t Count() const LOCKS_EXCLUDED(mu_);

  // Read returns the first message on the channel, subject to |max_size| checks.
  ReadResult Read(uint32_t max_size, uint32_t max_channels) LOCKS_EXCLUDED(mu_);

  // BlockingRead behaves like Read but blocks until a message is available.
  ReadResult BlockingRead(uint32_t max_size, uint32_t max_channels) LOCKS_EXCLUDED(mu_);

  // Write passes ownership of a message to the channel.
  void Write(std::unique_ptr<Message> msg) LOCKS_EXCLUDED(mu_);

  void Await() LOCKS_EXCLUDED(mu_);

  ReadResult ReadLocked(uint32_t max_size, uint32_t max_channels) EXCLUSIVE_LOCKS_REQUIRED(mu_);

  mutable absl::Mutex mu_;  // protects msgs_
  std::deque<std::unique_ptr<Message>> msgs_ GUARDED_BY(mu_);
};

// Shared-ownership wrapper for the read half of a MessageChannel.
class MessageChannelReadHalf {
 public:
  MessageChannelReadHalf(std::shared_ptr<MessageChannel> channel) : channel_(channel) {}

  std::unique_ptr<MessageChannelReadHalf> Clone() {
    return absl::make_unique<MessageChannelReadHalf>(channel_);
  }

  // Read a message from the channel, as long as the amount of data and handles
  // associated with the message fits within the specified limits.  The caller
  // owns any returned message, whose actual size / handle count will be less
  // than or equal to the specified limits.
  //
  // If the next available message on the channel does not fit in the specified
  // data/handle count limits, then no data will be returned and the ReadResult
  // will indicate the required sizes.
  //
  // Note that (pure) C++ users of this method can typically pass INT_MAX for
  // the limit parameters, as they receive ownership of the Message.
  ReadResult Read(uint32_t max_size, uint32_t max_channels) {
    return channel_->Read(max_size, max_channels);
  }

  // BlockingRead behaves like Read but blocks until a message is available.
  ReadResult BlockingRead(uint32_t max_size, uint32_t max_channels) {
    return channel_->BlockingRead(max_size, max_channels);
  }

  // Indicate whether a Read operation would return a message.
  bool CanRead() { return channel_->Count() > 0; }

  // Await blocks until there is a message available to read on the channel.
  void Await() { return channel_->Await(); }

 private:
  std::shared_ptr<MessageChannel> channel_;
};

// Shared-ownership wrapper for the write half of a MessageChannel.
class MessageChannelWriteHalf {
 public:
  MessageChannelWriteHalf(std::shared_ptr<MessageChannel> channel) : channel_(channel) {}

  std::unique_ptr<MessageChannelWriteHalf> Clone() {
    return absl::make_unique<MessageChannelWriteHalf>(channel_);
  }

  // Write the provided message to the Channel.
  void Write(std::unique_ptr<Message> msg) { channel_->Write(std::move(msg)); }

 private:
  std::shared_ptr<MessageChannel> channel_;
};

// Create a new channel half (of the same read/write end) that shares a
// reference to the same underlying MessageChannel.
std::unique_ptr<ChannelHalf> CloneChannelHalf(ChannelHalf* half);

// Current readable status of a channel.
struct ChannelStatus {
  explicit ChannelStatus(uint64_t h) : handle(h), ready(false) {}
  uint64_t handle;
  bool ready;
};

}  // namespace oak

#endif  // OAK_SERVER_CHANNEL_H_
