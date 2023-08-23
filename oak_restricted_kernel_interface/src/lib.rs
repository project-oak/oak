//
// Copyright 2022 The Project Oak Authors
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

#![no_std]

pub mod errno;
pub mod syscalls;

pub use errno::Errno;
pub use syscalls::Syscall;

/// Predefined file descriptor for the Oak communication channel.
pub const OAK_CHANNEL_FD: i32 = 0xa;

/// Predefined file descriptor for reading a derived key.
pub const DERIVED_KEY_FD: i32 = 0x21;
