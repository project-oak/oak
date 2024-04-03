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

#ifndef CC_CONTAINERS_SDK_COMMON_H_
#define CC_CONTAINERS_SDK_COMMON_H_

namespace oak::containers::sdk {

// Unix socket used to connect to the Orchestrator.
inline static const char kOrchestratorSocket[] =
    "unix:/oak_utils/orchestrator_ipc";

inline static const char kContextAuthority[] = "[::]:0";

}  // namespace oak::containers::sdk

#endif  // CC_CONTAINERS_COMMON_H_
