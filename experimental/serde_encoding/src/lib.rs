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

//! `serde` based serialization for inter-node communication.
//!
//! If your type is serializable using `serde` and implements `HandleVisit`, these functions can be
//! used to send those types to other Oak nodes, including any handles they might contain.
//!
//! ```
//! use oak::{handle::HandleVisit, io::Receiver};
//! use serde::{Deserialize, Serialize};
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
//! let msg = serde_encoding::encode(&test, bincode::serialize).unwrap();
//!
//! // Send `msg` to another node
//!
//! // On the recipient:
//! let decoded: Test = serde_encoding::decode(&msg, bincode::deserialize).unwrap();
//!
//! // Field values and handles are preserved
//! assert_eq!(test, decoded);
//! ```

use oak::{handle::HandleVisit, io::Message};

/// Encodes `value` in a [`Message`] using the given serialization function, preserving
/// any handles contained in `value`.
pub fn encode<T, B, E, F>(value: &T, serialize_fn: F) -> Result<Message, E>
where
    T: Clone + HandleVisit,
    B: Into<Vec<u8>>,
    F: FnOnce(&T) -> Result<B, E>,
{
    let mut value = value.clone();
    let handles = oak::handle::extract_handles(&mut value);
    let bytes = serialize_fn(&value)?.into();
    Ok(Message { bytes, handles })
}

/// Decodes `message` using the given deserialization function, injecting any handles in `message`
/// into the returned type.
pub fn decode<'a, T, E, F>(message: &'a Message, deserialize_fn: F) -> Result<T, DecodeError<E>>
where
    T: HandleVisit,
    F: FnOnce(&'a [u8]) -> Result<T, E>,
{
    let mut decoded = deserialize_fn(&message.bytes).map_err(DecodeError::Deserialize)?;
    oak::handle::inject_handles(&mut decoded, &message.handles).map_err(DecodeError::Inject)?;
    Ok(decoded)
}

/// Message decoding error.
#[derive(Debug)]
pub enum DecodeError<E> {
    Deserialize(E),
    Inject(oak::OakError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use oak::io::{Receiver, Sender};
    use serde::{Deserialize, Serialize};

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

        let msg = super::encode(&complex, bincode::serialize).unwrap();
        let decoded: ComplexType = super::decode(&msg, bincode::deserialize).unwrap();

        assert_eq!(complex, decoded);
    }
}
