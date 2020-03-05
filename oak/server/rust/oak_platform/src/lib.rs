//
// Copyright 2020 The Project Oak Authors
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

#![cfg_attr(feature = "no_std", no_std)]

#[cfg(feature = "asylo")]
pub use oak_platform_asylo::*;

#[cfg(feature = "std")]
mod imp {
    pub type Mutex<T> = std::sync::Mutex<T>;
    pub type RwLock<T> = std::sync::RwLock<T>;
    pub type JoinHandle = std::thread::JoinHandle<()>;
    pub type Thread = std::thread::Thread;
    pub type ThreadId = std::thread::ThreadId;

    pub use std::thread::current as current_thread;
    pub use std::thread::park as park_thread;
    pub use std::thread::spawn;
}
#[cfg(feature = "std")]
pub use imp::*;

/// An exported placeholder function to check that linking against C++ is successful.
#[no_mangle]
pub extern "C" fn add_magic_number(x: i32) -> i32 {
    x + 42
}
