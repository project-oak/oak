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
#include <set>
#include <unordered_map>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/synchronization/mutex.h"
#include "oak/common/handles.h"
#include "oak/server/channel.h"
#include "oak/server/labels.h"

namespace oak {

class OakNode {
 public:
  OakNode(const std::string& name, const OakLabels& labels)
      : name_(name), termination_pending_(false), next_handle_(0), labels_(labels) {}
  virtual ~OakNode();

  virtual void Start() = 0;
  virtual void Stop() = 0;

  // Add channel identified by the given port name to the node.  This must
  // only be called before the node is started (with Start()).
  Handle AddNamedChannel(const std::string& port_name, std::unique_ptr<ChannelHalf> half)
      LOCKS_EXCLUDED(mu_);

  // Take ownership of the given channel half, returning a channel handle that
  // the node can use to refer to it in future.
  Handle AddChannel(std::unique_ptr<ChannelHalf> half) LOCKS_EXCLUDED(mu_);

  // Close the given channel half.  Returns true if the channel was found and closed,
  // false if the channel was not found.
  bool CloseChannel(Handle handle) LOCKS_EXCLUDED(mu_);

  // Return a borrowed reference to the channel half identified by the given
  // handle (or nullptr if the handle is not recognized).  Caller is responsible
  // for ensuring that the borrowed reference does not out-live the owned
  // channel.
  ChannelHalf* BorrowChannel(Handle handle) const LOCKS_EXCLUDED(mu_);
  MessageChannelReadHalf* BorrowReadChannel(Handle handle) const LOCKS_EXCLUDED(mu_);
  MessageChannelWriteHalf* BorrowWriteChannel(Handle handle) const LOCKS_EXCLUDED(mu_);

  // Find the channel handle identified by the given port name.
  Handle FindChannel(const std::string& port_name) const LOCKS_EXCLUDED(mu_);

  // Wait on the given channel handles, modifying the contents of the passed-in
  // vector.  Returns a boolean indicating whether the wait finished due to a
  // channel being ready (true), or a failure (false, indicating either node
  // termination or no readable channels found).  Caller is responsible for
  // ensuring that none of the waited-on channels are closed during the wait
  // operation.
  bool WaitOnChannels(std::vector<std::unique_ptr<ChannelStatus>>* statuses) const;

  // Write the message to the (write) channel half identified by the handle,
  // attaching the Node's current labels to the message along the way.
  void Write(Handle handle, std::unique_ptr<Message> msg) const LOCKS_EXCLUDED(labels_mu_);

  // Perform a read on the (read) channel half identified by the handle.  Modify
  // this Node's labels according to any read message.
  ReadResult Read(Handle handle, uint32_t max_size, uint32_t max_channels)
      LOCKS_EXCLUDED(labels_mu_);

  // Perform a blocking read on the (read) channel half identified by the handle.
  // Modify this Node's labels according to any read message.
  ReadResult BlockingRead(Handle handle) LOCKS_EXCLUDED(labels_mu_);

 protected:
  const std::string name_;
  std::atomic_bool termination_pending_;

 private:
  using ChannelHalfTable = std::unordered_map<Handle, std::unique_ptr<ChannelHalf>>;

  mutable absl::Mutex mu_;  // protects next_handle_, named_channels_, channel_halves_,
                            // secrecy_labels_, integrity_labels_

  // Map from pre-configured port names to channel handles.
  Handle next_handle_ GUARDED_BY(mu_);
  std::unordered_map<std::string, Handle> named_channels_ GUARDED_BY(mu_);

  // Map from channel handles to channel half instances.
  ChannelHalfTable channel_halves_ GUARDED_BY(mu_);

  // Current set of secrecy and integrity labels for the Node.
  mutable absl::Mutex labels_mu_;
  OakLabels labels_ GUARDED_BY(labels_mu_);
};

}  // namespace oak

#endif  // OAK_SERVER_NODE_H_
