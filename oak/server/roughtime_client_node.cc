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

#include "oak/server/roughtime_client_node.h"

#include "absl/memory/memory.h"
#include "oak/common/logging.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/proto/roughtime_service.pb.h"
#include "oak/server/invocation.h"

using ::oak_abi::OakStatus;

namespace oak {

RoughtimeClientNode::RoughtimeClientNode(const std::string& name, NodeId node_id,
                                         const application::RoughtimeClientConfiguration& config)
    : OakNode(name, node_id) {
  std::vector<RoughtimeServerSpec> servers;
  for (const auto& server_conf : config.servers()) {
    RoughtimeServerSpec server;
    server.name = server_conf.name();
    server.host = server_conf.host();
    server.port = server_conf.port();
    server.public_key_base64 = server_conf.public_key_base64();
    servers.push_back(server);
  }
  client_ = absl::make_unique<RoughtimeClient>(servers, config.min_overlapping_intervals(),
                                               config.timeout_seconds(), config.server_retries(),
                                               config.max_radius_microseconds());
}

void RoughtimeClientNode::Run(Handle invocation_handle) {
  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(invocation_handle));
  while (true) {
    if (!WaitOnChannels(&channel_status)) {
      OAK_LOG(WARNING) << "Node termination requested";
      return;
    }

    std::unique_ptr<Invocation> invocation(Invocation::ReceiveFromChannel(this, invocation_handle));
    if (invocation == nullptr) {
      OAK_LOG(ERROR) << "Failed to create invocation";
      return;
    }

    // Expect to read a single request out of the request channel.
    NodeReadResult req_result = ChannelRead(invocation->req_handle.get());
    if (req_result.status != OakStatus::OK) {
      OAK_LOG(ERROR) << "Failed to read message: " << req_result.status;
      return;
    }
    if (req_result.msg->handles.size() != 0) {
      OAK_LOG(ERROR) << "Unexpectedly received channel handles in request channel";
      return;
    }
    // Ignore any data in the request message (as it's expected to be empty).

    // What's the time Mr. Wolf?
    oak::StatusOr<::roughtime::rough_time_t> time_or = client_->GetRoughTime();

    oak::encap::GrpcResponse grpc_rsp;
    if (!time_or.ok()) {
      OAK_LOG(ERROR) << "Failed to determine Roughtime: " << time_or.status().code() << ", '"
                     << time_or.status().message() << "'";
      grpc_rsp.mutable_status()->set_code(static_cast<int>(time_or.status().code()));
      grpc_rsp.mutable_status()->set_message(std::string(time_or.status().message()));
    } else {
      oak::roughtime::RoughTimeResponse rsp;
      rsp.set_rough_time_usec(time_or.ValueOrDie());
      rsp.SerializeToString(grpc_rsp.mutable_rsp_msg());
    }

    grpc_rsp.set_last(true);
    auto rsp_msg = absl::make_unique<NodeMessage>();
    size_t serialized_size = grpc_rsp.ByteSizeLong();
    rsp_msg->data.resize(serialized_size);
    grpc_rsp.SerializeToArray(rsp_msg->data.data(), rsp_msg->data.size());
    ChannelWrite(invocation->rsp_handle.get(), std::move(rsp_msg));

    // The response channel reference is dropped here.
  }
}

}  // namespace oak
