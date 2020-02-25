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

// TODO(#546): fix no_std
#![feature(result_contains_err)]
// #![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate no_std_compat as std;

pub mod proto;

pub mod channel;
pub mod config;
pub mod message;
pub mod node;
pub mod runtime;

#[cfg(test)]
mod tests;

pub use runtime::{ChannelEither, ChannelEitherOwned, ChannelReader, ChannelWriter};
pub use config::application_configuration;
pub use message::Message;
pub use runtime::{Runtime, RuntimeRef};

/// TODO(#546): Items here are not provided by `no-std-compat`. These need to be provided
/// by an external dependency i.e. asylo_rust when targeting asylo.
#[cfg(feature = "std")]
mod platform {
    pub type Mutex<T> = std::sync::Mutex<T>;
    pub type RwLock<T> = std::sync::RwLock<T>;
    pub use std::thread;
    pub type JoinHandle = std::thread::JoinHandle<()>;
}

use platform::*;
