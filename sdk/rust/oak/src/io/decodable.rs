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

use crate::{io::Message, OakError};

/// A trait for objects that can be decoded from bytes + handles.
pub trait Decodable: Sized {
    fn decode(message: &Message) -> Result<Self, OakError>;
}

impl<T: crate::handle::HandleVisit + prost::Message + Default> Decodable for T {
    fn decode(message: &Message) -> Result<Self, OakError> {
        let mut value = T::decode(message.bytes.as_slice())?;
        let handles: Vec<u64> = message.handles.to_vec();
        crate::handle::inject_handles(&mut value, &handles)?;
        Ok(value)
    }
}
