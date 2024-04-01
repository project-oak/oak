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

#include "absl/status/status.h"
#include "grpcpp/grpcpp.h"

namespace oak::transport {

absl::Status to_absl_status(const grpc::Status& grpc_status) {
  return absl::Status(static_cast<absl::StatusCode>(grpc_status.error_code()),
                      grpc_status.error_message());
}

}  // namespace oak::transport
