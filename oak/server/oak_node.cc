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

#include "oak/server/oak_node.h"

#include "absl/base/internal/endian.h"
#include "absl/memory/memory.h"
#include "oak/common/logging.h"
#include "oak/server/rust/oak_glue/oak_glue.h"

using ::oak_abi::ChannelReadStatus;
using ::oak_abi::OakStatus;

namespace oak {

NodeReadResult OakNode::ChannelRead(Handle handle) {
  uint32_t actual_size;
  uint32_t actual_count;
  uint32_t status =
      glue_channel_read(node_id_, handle, nullptr, 0, &actual_size, nullptr, 0, &actual_count);
  if ((status != OakStatus::ERR_BUFFER_TOO_SMALL) &&
      (status != OakStatus::ERR_HANDLE_SPACE_TOO_SMALL)) {
    return NodeReadResult(static_cast<OakStatus>(status));
  }
  NodeReadResult result(OakStatus::OK);
  result.msg = absl::make_unique<NodeMessage>();
  result.msg->data.resize(actual_size);
  result.msg->handles.resize(actual_count);
  status = glue_channel_read(node_id_, handle, reinterpret_cast<uint8_t*>(result.msg->data.data()),
                             actual_size, &actual_size,
                             reinterpret_cast<uint8_t*>(result.msg->handles.data()), actual_count,
                             &actual_count);
  result.status = static_cast<OakStatus>(status);
  return result;
}

OakStatus OakNode::ChannelWrite(Handle handle, std::unique_ptr<NodeMessage> msg) {
  uint32_t status = glue_channel_write(
      node_id_, handle, reinterpret_cast<const uint8_t*>(msg->data.data()), msg->data.size(),
      reinterpret_cast<const uint8_t*>(msg->handles.data()), msg->handles.size());
  return static_cast<OakStatus>(status);
}

std::pair<Handle, Handle> OakNode::ChannelCreate() {
  uint64_t write;
  uint64_t read;
  uint32_t status = glue_channel_create(node_id_, &write, &read);
  if (static_cast<OakStatus>(status) != OakStatus::OK) {
    return std::pair<Handle, Handle>(0, 0);
  }
  return std::pair<Handle, Handle>(write, read);
}

OakStatus OakNode::ChannelClose(Handle handle) {
  uint32_t status = glue_channel_close(node_id_, handle);
  return static_cast<OakStatus>(status);
}

bool OakNode::WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const {
  int count = statuses->size();
  std::vector<uint8_t> space(kSpaceBytesPerHandle * count);
  for (int ii = 0; ii < count; ii++) {
    Handle handle = (*statuses)[ii]->handle;
    OAK_LOG(INFO) << "{" << name_ << "} wait on " << handle;
    absl::little_endian::Store64(space.data() + (kSpaceBytesPerHandle * ii), handle);
  }
  uint32_t status = glue_wait_on_channels(node_id_, space.data(), count);
  for (int ii = 0; ii < count; ii++) {
    (*statuses)[ii]->status =
        static_cast<ChannelReadStatus>(space[kSpaceBytesPerHandle * ii + sizeof(uint64_t)]);
  }
  return (status == OakStatus::OK);
}

}  // namespace oak
