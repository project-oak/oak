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

#include "absl/status/statusor.h"
#include "cc/crypto/hpke/recipient_context.h"
#include "proto/session/messages.pb.h"

#ifndef CC_CONTAINERS_SDK_STANDALONE_OAK_STANDALONE_H_
#define CC_CONTAINERS_SDK_STANDALONE_OAK_STANDALONE_H_

namespace oak::containers::sdk::standalone {

/// Get an instance of EndorsedEvidence that's valid to use in an Oak Standalone
/// application.
///
/// The resulting EndorsedEvidence will contain the public keys from the
/// provided KeyPair.
absl::StatusOr<session::v1::EndorsedEvidence> GetEndorsedEvidence(
    const oak::crypto::KeyPair& key_pair);

}  // namespace oak::containers::sdk::standalone

#endif  // CC_CONTAINERS_SDK_STANDALONE_OAK_STANDALONE_H_
