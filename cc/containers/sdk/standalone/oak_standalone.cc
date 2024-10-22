/*
 * Copyright 2024 The Project Oak Authors
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

#include "cc/containers/sdk/standalone/oak_standalone.h"

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "proto/session/messages.pb.h"

extern "C" {
extern bool standalone_endorsed_evidence(void*,
                                         bool (*f)(void*, char*, uint32_t));
}

namespace oak::containers::sdk::standalone {

using oak::session::v1::EndorsedEvidence;

namespace {

/// This is the callback that we pass to the Rust code.
///
/// During the scope of this callback invocation, we can process the data
/// however we need, but anything we want to hold onto needs to be copied.
///
/// The context object is a pointer to the EndorsedEvidence to populate.
bool DeserializeEndorsedEvidence(void* evidence, char* data, uint32_t size) {
  LOG(INFO) << "trying to interpret proto data of size " << size;
  return (static_cast<EndorsedEvidence*>(evidence))->ParseFromArray(data, size);
}

}  // namespace

absl::StatusOr<EndorsedEvidence> GetEndorsedEvidence() {
  EndorsedEvidence evidence;
  if (!standalone_endorsed_evidence(&evidence, DeserializeEndorsedEvidence)) {
    return absl::InternalError("Failed to get endorsed evidence");
  }
  return evidence;
}

}  // namespace oak::containers::sdk::standalone