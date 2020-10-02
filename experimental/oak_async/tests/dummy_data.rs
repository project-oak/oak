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
use oak::{
    io::{Decodable, Encodable, Message},
    OakError,
};

/// Wrapper around `String` to make it implement `Encodable` and `Decodable`.
///
/// Used as a dummy message payload.
#[derive(Debug, PartialEq)]
pub struct DummyData(pub String);

impl DummyData {
    pub fn new(s: &str) -> DummyData {
        DummyData(s.into())
    }
}

impl Encodable for DummyData {
    fn encode(&self) -> Result<Message, OakError> {
        Ok(Message {
            bytes: self.0.clone().into_bytes(),
            handles: Vec::new(),
        })
    }
}

impl Decodable for DummyData {
    fn decode(message: &Message) -> Result<Self, OakError> {
        assert!(
            message.handles.is_empty(),
            "DummyData must not have handles"
        );
        Ok(String::from_utf8(message.bytes.clone())
            .map(DummyData)
            .expect("Failed to decode DummyData"))
    }
}
