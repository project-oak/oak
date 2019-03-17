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

#ifndef OAK_GRPC_SERVER_GRPC_EVENT_H_
#define OAK_GRPC_SERVER_GRPC_EVENT_H_

#include "grpc_stream.h"

namespace oak {
namespace grpc_server {

// Representation of a gRPC event.
//
// An event object is added to the gRPC completion queue once an event is
// completed. Then handle() is called to invoke any subsequent dependent
// work.
class BaseGrpcEvent {
 public:
  virtual void handle() = 0;

 protected:
  BaseGrpcEvent(std::shared_ptr<GrpcStream> stream_) : stream_(stream_) {}
  std::shared_ptr<GrpcStream> stream_;
};

// Event: A new gRPC stream was created (new RPC).
class StreamCreationEvent : BaseGrpcEvent {
 public:
  StreamCreationEvent(std::shared_ptr<GrpcStream> stream_) : BaseGrpcEvent(stream_) {}
  void handle() override;
};

// Event: Completed reading the request.
class RequestReadEvent : BaseGrpcEvent {
 public:
  RequestReadEvent(std::shared_ptr<GrpcStream> stream_) : BaseGrpcEvent(stream_) {}
  void handle() override;
};

// Event: Completed writing the response.
class ResponseWrittenEvent : BaseGrpcEvent {
 public:
  ResponseWrittenEvent(std::shared_ptr<GrpcStream> stream_) : BaseGrpcEvent(stream_) {}
  void handle() override;
};

}  // namespace grpc_server
}  // namespace oak

#endif  // OAK_GRPC_SERVER_GRPC_EVENT_H_
