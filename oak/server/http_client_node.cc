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

#include "oak/server/http_client_node.h"

#include "absl/memory/memory.h"
#include "asylo/util/logging.h"
#include "grpcpp/create_channel.h"
#include "oak/common/app_config.h"
#include "oak/proto/grpc_encap.pb.h"
#include "oak/proto/http_client.pb.h"

namespace oak {

HttpClientNode::HttpClientNode(const std::string& name, const std::string& url,
                               const std::string& method)
    : NodeThread(name), url_(url), method_(method) {}

void HttpClientNode::Run() {
  Handle request_handle = FindChannel(kHttpClientNodeRequestPortName);
  Handle response_handle = FindChannel(kHttpClientNodeResponsePortName);
  MessageChannelReadHalf* request_channel = BorrowReadChannel(request_handle);
  MessageChannelWriteHalf* response_channel = BorrowWriteChannel(response_handle);
  if (request_channel == nullptr || response_channel == nullptr) {
    LOG(ERROR) << "Required channel not available; handles: " << request_handle << ", "
               << response_handle;
  }
  std::vector<std::unique_ptr<ChannelStatus>> channel_status;
  channel_status.push_back(absl::make_unique<ChannelStatus>(request_handle));
  while (true) {
    if (!WaitOnChannels(&channel_status)) {
      LOG(WARNING) << "Node termination requested";
      return;
    }

    ReadResult result = request_channel->Read(INT_MAX, INT_MAX);
    if (result.required_size > 0) {
      LOG(ERROR) << "Message size too large: " << result.required_size;
      return;
    }

    GrpcRequest channel_request;
    channel_request.ParseFromString(std::string(result.msg->data.data(), result.msg->data.size()));
    GrpcResponse channel_response;
    grpc::Status status;
    std::string method_name = channel_request.method_name();

    if (method_name == "/oak.HttpClient/Send") {
      HttpClientSendRequest channel_read_request;
      if (!channel_request.req_msg().UnpackTo(&channel_read_request)) {
        // TODO: Handle errors.
      }
      HttpClientSendResponse channel_read_response;

      // TODO: make http request

      channel_response.mutable_rsp_msg()->PackFrom(channel_read_response);
    }
  }
}

}  // namespace oak
