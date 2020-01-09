//
// Copyright 2019 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! Type and constant definitions for the Oak application binary interface.

pub use proto::oak_api::ChannelReadStatus;
pub use proto::oak_api::OakStatus;

pub mod proto;

/// Number of bytes needed per-handle for channel readiness notifications.
///
/// The notification space consists of the channel handle (as a little-endian
/// u64) followed by a single byte indicating the channel readiness, as
/// a `ChannelReadStatus` value.
pub const SPACE_BYTES_PER_HANDLE: usize = 9;

/// Invalid handle value.
pub const INVALID_HANDLE: u64 = 0;
