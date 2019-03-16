/*
 * Copyright 2018 The Project Oak Authors
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

class GrpcEvent {
  public:
  enum EventType {
    NEW_STREAM,
    REQUEST_READ,
    RESPONSE_WRITTEN,
    UNKNOWN,
  };

  GrpcEvent(EventType event, GrpcStream* stream) : event_(event), stream_(stream) {}

  GrpcStream* stream() { return stream_; }

  EventType event() const { return event_; }

 private:
  EventType event_;
  GrpcStream* stream_;
};
}  // namespace grpc_server
}  // namespace oak

#endif  // OAK_GRPC_SERVER_GRPC_EVENT_H_
