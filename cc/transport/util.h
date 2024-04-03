/*
 * Copyright 2023 The Project Oak Authors
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

#ifndef CC_TRANSPORT_UTIL_H_
#define CC_TRANSPORT_UTIL_H_

#include "absl/status/status.h"
#include "grpcpp/grpcpp.h"

namespace oak::transport {

// Converts gRPC status to an absl status. The gRPC error status code is casted
// and the error message is copied.
absl::Status to_absl_status(const grpc::Status& grpc_status);

}  // namespace oak::transport

#endif  // CC_TRANSPORT_UTIL_H_
