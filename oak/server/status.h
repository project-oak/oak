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

#ifndef OAK_SERVER_STATUS_H_
#define OAK_SERVER_STATUS_H_

namespace oak {

using OakStatus = int32_t;

// The following status values are returned from Oak host functions.
// Keep in sync with /rust/oak/src/lib.rs.

// Success.
const OakStatus STATUS_OK = 0;
// Invalid handle provided.
const OakStatus STATUS_ERR_BAD_HANDLE = 1;
// Arguments invalid.
const OakStatus STATUS_ERR_INVALID_ARGS = 2;
// Channel has been closed.
const OakStatus STATUS_ERR_CHANNEL_CLOSED = 3;
// Provided buffer was too small for operation (an output value will indicate required size).
const OakStatus STATUS_ERR_BUFFER_TOO_SMALL = 4;
// Argument out of valid range.
const OakStatus STATUS_ERR_OUT_OF_RANGE = 5;

}  // namespace oak

#endif  // OAK_SERVER_STATUS_H_
