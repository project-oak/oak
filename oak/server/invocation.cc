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

#include "oak/common/logging.h"

using ::oak_abi::OakStatus;

namespace oak {

std::unique_ptr<Invocation> Invocation::ReceiveFromChannel(OakNode* node,
                                                           Handle invocation_handle) {
  // Expect to receive a pair of channel handles:
  //  - Handle for the read half of a channel that holds the request, serialized
  //    as a GrpcRequest.
  //  - Handle for the write half of a channel to send responses down, each
  //    serialized as a GrpcResponse.
  NodeReadResult invocation = node->ChannelRead(invocation_handle, INT_MAX, INT_MAX);
  if (invocation.status != OakStatus::OK) {
    OAK_LOG(ERROR) << "Failed to read invocation message: " << invocation.status;
    return nullptr;
  }
  if (invocation.msg->data.size() != 0) {
    OAK_LOG(ERROR) << "Unexpectedly received data in invocation";
    return nullptr;
  }
  if (invocation.msg->handles.size() != 2) {
    OAK_LOG(ERROR) << "Wrong number of handles " << invocation.msg->handles.size()
                   << " in invocation";
    return nullptr;
  }
  return absl::make_unique<Invocation>(node, invocation.msg->handles[0],
                                       invocation.msg->handles[1]);
}

}  // namespace oak
