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

namespace oak {

// Abstract interface for Oak communication channels.
//
// A Channel represents a uni-directional stream of bytes, similar to a TCP socket. Each
// Channel has two halves, a send half and a receive half.  A channel half is represented
// by a common ChannelHalf type so that they can be referenced from a common numbering
// space, even though the send and receive halves have distinct functionality.
//
// No message framing or flow control is implemented at this level; application
// may decide to build some of these abstractions on top of the Channel
// interface.  In particular, a single Read is not guaranteed to return an
// entire message as one piece, and a single Write is not guaranteed to write
// the entire message in one piece.
//
// See https://blog.stephencleary.com/2009/04/message-framing.html
//
// Each channel may be connected to a built-in component, or to a local or remote Oak Node.
class ChannelHalf {
 public:
  virtual ~ChannelHalf() {}

  // Read |size| bytes from the Channel. The actual size of the data read may be less than |size|.
  // An attempt to read from the send half of a channel will reach this fallback implementation
  // and always return an empty slice.
  virtual absl::Span<const char> Read(uint32_t size) {
    absl::Span<const char> empty;
    return empty;
  }

  // Write the provided bytes to the Channel. Return the number of bytes actually written.
  // An attempt to write to the receive half of a channel will reach this fallback implementation
  // and always return zero bytes.
  virtual uint32_t Write(absl::Span<const char> data) { return 0; }
};

}  // namespace oak

#endif  // OAK_SERVER_CHANNEL_H_
