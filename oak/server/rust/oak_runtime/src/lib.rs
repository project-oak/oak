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

#![feature(result_contains_err)]

#[cfg(feature = "no_std")]
extern crate no_std_compat as std;

#[cfg(feature = "std")]
pub mod proto;

// pub mod channel;
#[cfg(feature = "std")]
pub mod config;
pub mod message;
pub mod node;
pub mod runtime;

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
pub use config::application_configuration;
#[cfg(feature = "std")]
pub use config::configure_and_run;

pub use message::Message;
pub use runtime::{ChannelEither, ChannelReader, ChannelWriter, Runtime, RuntimeRef};
