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

//! `serde` based serialization formats for inter-node communication.
//!
//! If your type is serializable using `serde` and implements `HandleVisit`, these formats can be
//! used to send those types to other Oak nodes, including any handles they might contain.
//!
//! ```
//! use oak::{
//!     handle::HandleVisit,
//!     io::{Decodable, Encodable, Receiver},
//! };
//! use serde::{Deserialize, Serialize};
//! use serde_encoding::Bincoded;
//!
//! #[derive(Clone, Serialize, Deserialize, HandleVisit, Debug, PartialEq)]
//! struct Test {
//!     a: String,
//!     b: Receiver<()>,
//! }
//!
//! let test = Test {
//!     a: "Hello, world!".to_string(),
//!     b: Receiver::new(oak::ReadHandle { handle: 42 }),
//! };
//! let bincoded = Bincoded(test);
//! let msg = bincoded.encode().unwrap();
//!
//! // Send `msg` to another node
//!
//! // On the recipient:
//! let decoded: Bincoded<Test> = Bincoded::decode(&msg).unwrap();
//!
//! // Field values and handles are preserved
//! assert_eq!(decoded.0, bincoded.0);
//! ```

use oak::{
    handle::HandleVisit,
    io::{Decodable, Encodable, Message},
    OakError,
};
use serde::{Deserialize, Serialize};

/// [`bincode`](https://crates.io/crates/bincode) format.
pub struct Bincoded<T>(pub T);

impl<T: Clone + Serialize + HandleVisit> Encodable for Bincoded<T> {
    fn encode(&self) -> Result<Message, OakError> {
        Ok(Message {
            bytes: bincode::serialize(&self.0).map_err(|_| OakError::ProtobufEncodeError(None))?,
            handles: oak::handle::extract_handles(&mut self.0.clone()),
        })
    }
}

impl<T: for<'de> Deserialize<'de> + HandleVisit> Decodable for Bincoded<T> {
    fn decode(message: &Message) -> Result<Self, OakError> {
        let mut decoded = bincode::deserialize(message.bytes.as_slice())
            .map_err(|_| OakError::ProtobufDecodeError(None))?;
        oak::handle::inject_handles(&mut decoded, &message.handles)?;
        Ok(Bincoded(decoded))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oak::io::{Encodable, Receiver, Sender};

    #[derive(Clone, Serialize, Deserialize, HandleVisit, Debug, PartialEq)]
    struct ComplexInnerType {
        receiver: Receiver<()>,
        field_c: i32,
    }

    #[derive(Clone, Serialize, Deserialize, HandleVisit, Debug, PartialEq)]
    struct ComplexType {
        field_a: String,
        receiver: Receiver<()>,
        field_b: u64,
        sender: Sender<()>,
        inner: Vec<ComplexInnerType>,
    }

    #[test]
    fn roundtrip_complex_type() {
        let complex = ComplexType {
            field_a: "A".to_string(),
            receiver: Receiver::new(oak::ReadHandle { handle: 1 }),
            field_b: 2,
            sender: Sender::new(oak::WriteHandle { handle: 3 }),
            inner: vec![
                ComplexInnerType {
                    receiver: Receiver::new(oak::ReadHandle { handle: 6 }),
                    field_c: 7,
                },
                ComplexInnerType {
                    receiver: Receiver::new(oak::ReadHandle { handle: 4 }),
                    field_c: 5,
                },
            ],
        };

        let bincoded = Bincoded(complex);
        let msg = bincoded.encode().unwrap();
        let decoded: Bincoded<ComplexType> = Bincoded::decode(&msg).unwrap();

        assert_eq!(decoded.0, bincoded.0);
    }
}
