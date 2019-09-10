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
#include "absl/synchronization/mutex.h"
#include "absl/types/span.h"

namespace oak {

using Message = std::vector<char>;

// Result of a read operation. If the operation would have produced a message
// bigger than the requested maximum size, then |required_size| will be
// non-zero and indicates the required size for the message.  Otherwise,
// |required_size| will be zero and |data| holds the message (transferring
// ownership).
struct ReadResult {
  uint32_t required_size;
  std::unique_ptr<Message> data;
};

// Abstract interface for Oak communication channels.
//
// A Channel represents a uni-directional stream of messages. Each Channel has
// two halves, a send half and a receive half.  A channel half is represented by
// a common ChannelHalf type so that they can be referenced from a common
// numbering space, even though the send and receive halves have distinct
// functionality.
//
// No flow control is implemented at this level; application
// may decide to build some of these abstractions on top of the Channel
// interface.
//
// Each channel may be connected to a built-in component, or to a local or
// remote Oak Node.
//
// TODO: add a hard limit for message size
class ChannelHalf {
 public:
  virtual ~ChannelHalf() {}

  // Read a message of up to |size| bytes from the Channel. The caller owns any
  // returned message, whose actual size of may be less than |size|.  If the
  // next available message on the channel is larger than |size|, no data will
  // be returned and the required_size field of the result will indicate the
  // required size.
  virtual ReadResult Read(uint32_t size) {
    // Fallback implementation that returns an empty message; attempting to
    // read from the send half of a channel will reach this fallback.
    ReadResult nothing;
    nothing.required_size = 0;
    return nothing;
  }

  // BlockingRead behaves like Read but blocks until a message is available.
  virtual ReadResult BlockingRead(uint32_t size) { return Read(size); }

  // Indicate whether a Read operation would return a message.
  virtual bool CanRead() { return false; }

  // Write the provided message to the Channel.
  virtual void Write(std::unique_ptr<Message> msg) {
    // Fallback implementation that just drops the message.
  }

  // Await blocks until there is a message available to read on the channel.
  virtual void Await() {}
};

// A concrete message channel, which holds an arbitrary number of queued messages.
// Implements both send and receive ChannelHalf functions, though callers should wrap instances of
// this class into the appropriate ChannelHalf implementation (|MessageChannelReadHalf| or
// |MessageChannelWriteHalf|) to interact with it.
// TODO: Clean up this interface, e.g. hide the Read and Write methods on MessageChannel and expose
// methods to get access to the read and write halves instead.
class MessageChannel final : public ChannelHalf {
 public:
  // Count indicates the number of pending messages.
  size_t Count() const LOCKS_EXCLUDED(mu_);

  // Read returns the first message on the channel, subject to |size| checks.
  ReadResult Read(uint32_t size) override LOCKS_EXCLUDED(mu_);

  // BlockingRead behaves like Read but blocks until a message is available.
  ReadResult BlockingRead(uint32_t size) override LOCKS_EXCLUDED(mu_);

  // Write passes ownership of a message to the channel.
  void Write(std::unique_ptr<Message> data) override LOCKS_EXCLUDED(mu_);

  void Await() override LOCKS_EXCLUDED(mu_);

 private:
  ReadResult ReadLocked(uint32_t size) EXCLUSIVE_LOCKS_REQUIRED(mu_);

  mutable absl::Mutex mu_;  // protects msgs_
  std::deque<std::unique_ptr<Message>> msgs_ GUARDED_BY(mu_);
};

// Shared-ownership wrapper for the read half of a MessageChannel.
class MessageChannelReadHalf final : public ChannelHalf {
 public:
  MessageChannelReadHalf(std::shared_ptr<MessageChannel> channel) : channel_(channel) {}
  ReadResult Read(uint32_t size) override { return channel_->Read(size); }
  bool CanRead() override { return channel_->Count() > 0; }
  ReadResult BlockingRead(uint32_t size) override { return channel_->BlockingRead(size); }
  void Await() override { return channel_->Await(); }

 private:
  std::shared_ptr<MessageChannel> channel_;
};

// Shared-ownership wrapper for the write half of a MessageChannel.
class MessageChannelWriteHalf final : public ChannelHalf {
 public:
  MessageChannelWriteHalf(std::shared_ptr<MessageChannel> channel) : channel_(channel) {}
  void Write(std::unique_ptr<Message> msg) override { channel_->Write(std::move(msg)); }

 private:
  std::shared_ptr<MessageChannel> channel_;
};

// Current readable status of a channel.
struct ChannelStatus {
  explicit ChannelStatus(uint64_t h) : handle(h) {}
  uint64_t handle;
  bool ready;
};

}  // namespace oak

#endif  // OAK_SERVER_CHANNEL_H_
