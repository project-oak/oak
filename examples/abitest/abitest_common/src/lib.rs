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

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct InternalMessage {
    pub msg: String,
}

impl oak::io::Encodable for InternalMessage {
    fn encode(&self) -> Result<oak::io::Message, oak::OakError> {
        let bytes = serde_json::to_string(&self)
            .expect("could not serialize message to JSON")
            .into_bytes();
        let handles = Vec::new();
        Ok(oak::io::Message { bytes, handles })
    }
}
