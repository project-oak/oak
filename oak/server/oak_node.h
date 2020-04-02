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

#ifndef OAK_SERVER_NODE_H_
#define OAK_SERVER_NODE_H_

#include <stdint.h>

#include <memory>
#include <vector>

#include "oak/common/handles.h"
#include "oak/proto/label.pb.h"
#include "oak/proto/oak_abi.pb.h"

namespace oak {

// Current readable status of a channel.
struct ChannelStatus {
  explicit ChannelStatus(uint64_t h) : handle(h), status(oak_abi::ChannelReadStatus::NOT_READY) {}
  uint64_t handle;
  oak_abi::ChannelReadStatus status;
};

// Representation of a message transferred over a channel, relative to
// a particular Node.
struct NodeMessage {
  std::vector<char> data;
  std::vector<Handle> handles;
  oak::label::Label label;
};

// Result of a read operation relative to a Node.
struct NodeReadResult {
  explicit NodeReadResult(oak_abi::OakStatus s) : status(s) {}
  oak_abi::OakStatus status;
  // The following field is filled in if the status is OK.
  std::unique_ptr<NodeMessage> msg;
};

using NodeId = uint64_t;

class OakNode {
 public:
  OakNode(const std::string& name, NodeId node_id) : name_(name), node_id_(node_id) {}
  virtual ~OakNode() {}

  // The Run() method is run on a new thread, and should respond to termination
  // requests (indicated by termination_pending_.load()) in a timely manner.
  virtual void Run(Handle handle) = 0;

  // ChannelRead returns the first message on the channel identified by the
  // handle.
  NodeReadResult ChannelRead(Handle handle);

  // ChannelWrite passes ownership of a message to the channel identified by the
  // handle.
  oak_abi::OakStatus ChannelWrite(Handle handle, std::unique_ptr<NodeMessage> msg);

  // Create a channel and return the (write, read) handles for it.
  std::pair<Handle, Handle> ChannelCreate();

  // Close the given channel half.
  oak_abi::OakStatus ChannelClose(Handle handle);

  // Wait on the given channel handles, modifying the contents of the passed-in
  // vector.  Returns a boolean indicating whether the wait finished due to a
  // channel being ready (true), or a failure (false, indicating either node
  // termination or no readable channels found).  Caller is responsible for
  // ensuring that none of the waited-on channels are closed during the wait
  // operation.
  bool WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const;

 protected:
  const std::string name_;
  const NodeId node_id_;

 private:
  // Allow the Runtime to use internal methods.
  friend class OakRuntime;
};

}  // namespace oak

#endif  // OAK_SERVER_NODE_H_
