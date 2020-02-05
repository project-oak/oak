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

use crate::io::Message;
use crate::OakError;

/// A trait for objects that can be encoded as bytes + handles.
pub trait Encodable {
    fn encode(&self) -> Result<Message, OakError>;
}

impl<T: protobuf::Message> Encodable for T {
    fn encode(&self) -> Result<Message, OakError> {
        let bytes = self.write_to_bytes()?;
        let handles = Vec::new();
        Ok(crate::io::Message { bytes, handles })
    }
}
