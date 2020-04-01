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

#include <atomic>
#include <memory>
#include <random>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/synchronization/mutex.h"
#include "oak/common/handles.h"
#include "oak/server/base_runtime.h"
#include "oak/server/channel.h"

namespace oak {

// Representation of a message transferred over a channel, relative to
// a particular Node.  This is equivalent to the Message object, but
// using channel handles (which are relative to a particular OakNode) rather
// than raw channel references.
struct NodeMessage {
  std::vector<char> data;
  std::vector<Handle> handles;
  oak::policy::Label label;
};

// Result of a read operation relative to a Node. Equivalent to ReadResult but
// holds a NodeMessage rather than a Message.
struct NodeReadResult {
  explicit NodeReadResult(OakStatus s) : status(s), required_size(0), required_channels(0) {}
  OakStatus status;
  // The following fields are filled in if the status is ERR_BUFFER_TOO_SMALL
  // or ERR_HANDLE_SPACE_TOO_SMALL, indicating the required size and number
  // of handles needed to read the message.
  uint32_t required_size;
  uint32_t required_channels;
  // The following field is filled in if the status is OK.
  std::unique_ptr<NodeMessage> msg;
};

class OakNode {
 public:
  OakNode(BaseRuntime* runtime, const std::string& name)
      : name_(name), runtime_(runtime), prng_engine_() {}
  virtual ~OakNode() {}

  virtual void Start(Handle handle) = 0;
  virtual void Stop() = 0;

  // ChannelRead returns the first message on the channel identified by the
  // handle, subject to size checks.
  NodeReadResult ChannelRead(Handle handle, uint32_t max_size, uint32_t max_channels);

  // ChannelWrite passes ownership of a message to the channel identified by the
  // handle.
  OakStatus ChannelWrite(Handle handle, std::unique_ptr<NodeMessage> msg);

  // Create a channel and return the (write, read) handles for it.
  std::pair<Handle, Handle> ChannelCreate();

  // Close the given channel half.
  OakStatus ChannelClose(Handle handle) LOCKS_EXCLUDED(mu_);

  // Create a new Node.
  OakStatus NodeCreate(Handle handle, const std::string& config_name,
                       const std::string& entrypoint_name);

  // Wait on the given channel handles, modifying the contents of the passed-in
  // vector.  Returns a boolean indicating whether the wait finished due to a
  // channel being ready (true), or a failure (false, indicating either node
  // termination or no readable channels found).  Caller is responsible for
  // ensuring that none of the waited-on channels are closed during the wait
  // operation.
  bool WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const;

 protected:
  bool TerminationPending() const { return runtime_->TerminationPending(); }

  void ClearHandles() LOCKS_EXCLUDED(mu_);

  const std::string name_;

 private:
  // Allow the Runtime to use internal methods.
  friend class OakRuntime;

  // Take ownership of the given channel half, returning a channel handle that
  // the Node can use to refer to it in future.
  Handle AddChannel(std::unique_ptr<ChannelHalf> half) LOCKS_EXCLUDED(mu_);

  Handle NextHandle() EXCLUSIVE_LOCKS_REQUIRED(mu_);

  // Return a borrowed reference to the channel half identified by the given
  // handle (or nullptr if the handle is not recognized).  Caller is responsible
  // for ensuring that the borrowed reference does not out-live the owned
  // channel.
  ChannelHalf* BorrowChannel(Handle handle) const LOCKS_EXCLUDED(mu_);
  MessageChannelReadHalf* BorrowReadChannel(Handle handle) const LOCKS_EXCLUDED(mu_);
  MessageChannelWriteHalf* BorrowWriteChannel(Handle handle) const LOCKS_EXCLUDED(mu_);

  using ChannelHalfTable = std::unordered_map<Handle, std::unique_ptr<ChannelHalf>>;

  // Runtime instance that owns this Node.
  BaseRuntime* const runtime_;

  mutable absl::Mutex mu_;  // protects prng_engine_, channel_halves_

  std::random_device prng_engine_ GUARDED_BY(mu_);

  // Map from channel handles to channel half instances.
  ChannelHalfTable channel_halves_ GUARDED_BY(mu_);
};

}  // namespace oak

#endif  // OAK_SERVER_NODE_H_
