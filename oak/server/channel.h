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

#include "absl/types/span.h"

namespace oak {

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
  // Result of a read operation. If not enough space was provided for the
  // message, then |required_size| will be non-zero and indicates the required size.
  // Otherwise, |required_size| will be zero and |data| references the data of the
  // message that has been read.
  struct ReadResult {
    uint32_t required_size;
    absl::Span<const char> data;
  };

  virtual ~ChannelHalf() {}

  // Read a message of up to |size| bytes from the Channel. The actual size of
  // the returned message may be less than |size|.  If the next available
  // message on the channel is larger than |size|, no data will be returned
  // and the required_size field of the result will indicate the required size.
  virtual ReadResult Read(uint32_t size) {
    // Fallback implementation that returns an empty message; attempting to
    // read from the send half of a channel will reach this fallback.
    ReadResult nothing;
    nothing.required_size = 0;
    return nothing;
  }

  // Write the provided message to the Channel. Return the number of bytes
  // actually written, which will either be zero or the size of the provided
  // message.
  virtual uint32_t Write(absl::Span<const char> data) {
    // Fallback implementation that indicates nothing was written; attempting to
    // write to the receive half of a channel will reach this fallback.
    return 0;
  }
};

}  // namespace oak

#endif  // OAK_SERVER_CHANNEL_H_
