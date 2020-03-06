/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/server/invocation.h"

#include "absl/memory/memory.h"
#include "oak/common/logging.h"

namespace oak {

std::unique_ptr<Invocation> Invocation::ReceiveFromChannel(
    MessageChannelReadHalf* invocation_channel) {
  // Expect to receive a pair of channel references:
  //  - Reference to the read half of a channel that holds the request, serialized
  //    as a GrpcRequest.
  //  - Reference to the write half of a channel to send responses down, each
  //    serialized as a GrpcResponse.
  ReadResult invocation = invocation_channel->Read(INT_MAX, INT_MAX);
  if (invocation.required_size > 0) {
    OAK_LOG(ERROR) << "Message size too large: " << invocation.required_size;
    return nullptr;
  }
  if (invocation.msg->data.size() != 0) {
    OAK_LOG(ERROR) << "Unexpectedly received data in invocation";
    return nullptr;
  }
  if (invocation.msg->channels.size() != 2) {
    OAK_LOG(ERROR) << "Wrong number of channels " << invocation.msg->channels.size()
                   << " in invocation";
    return nullptr;
  }

  std::unique_ptr<ChannelHalf> half0 = std::move(invocation.msg->channels[0]);
  auto channel0 = absl::get_if<std::unique_ptr<MessageChannelReadHalf>>(half0.get());
  if (channel0 == nullptr) {
    OAK_LOG(ERROR) << "First channel accompanying invocation is write-direction";
    return nullptr;
  }

  std::unique_ptr<ChannelHalf> half1 = std::move(invocation.msg->channels[1]);
  auto channel1 = absl::get_if<std::unique_ptr<MessageChannelWriteHalf>>(half1.get());
  if (channel1 == nullptr) {
    OAK_LOG(ERROR) << "Second channel accompanying invocation is read-direction";
    return nullptr;
  }
  return absl::make_unique<Invocation>(std::move(*channel0), std::move(*channel1));
}

}  // namespace oak
