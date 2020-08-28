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

//! Shared data structures and functionality for inter-node communication.

mod decodable;
mod encodable;
mod error;
pub mod handle;
mod receiver;
mod sender;

pub use decodable::Decodable;
pub use encodable::Encodable;
pub use error::OakError;
use handle::{ReadHandle, WriteHandle};
pub use oak_abi::Handle;
pub use receiver::Receiver;
pub use sender::Sender;

/// A simple holder for bytes + handles, using internally owned buffers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message {
    pub bytes: Vec<u8>,
    pub handles: Vec<Handle>,
}
