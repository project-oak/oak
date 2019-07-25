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
#include <memory>
#include <vector>

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

  // Write the provided message to the Channel.
  virtual void Write(std::unique_ptr<Message> msg) {
    // Fallback implementation that just drops the message.
  }
};

}  // namespace oak

#endif  // OAK_SERVER_CHANNEL_H_
