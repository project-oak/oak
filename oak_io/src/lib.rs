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
use either::Either;
pub use encodable::Encodable;
pub use error::OakError;
use handle::{ReadHandle, WriteHandle};
pub use oak_abi::{Handle, OakStatus};
pub use receiver::Receiver;
pub use sender::Sender;

/// A simple holder for bytes + handles, using internally owned buffers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message {
    pub bytes: Vec<u8>,
    pub handles: Vec<Handle>,
}

/// Implementation of [`Encodable`] for [`Either`] that encodes the variant (0 or 1) in the first
/// byte of the resulting [`Message`].
impl<L: Encodable, R: Encodable> Encodable for Either<L, R> {
    fn encode(&self) -> Result<Message, OakError> {
        let (variant, mut inner) = match self {
            // Left variant == 0.
            Either::Left(m) => (0, m.encode()?),
            // Right variant == 1.
            Either::Right(m) => (1, m.encode()?),
        };
        // Insert the variant byte as the beginning of the message bytes, and leave handles as they
        // are.
        inner.bytes.insert(0, variant);
        Ok(inner)
    }
}

/// Implementation of [`Decodable`] for [`Either`] that decodes the variant (0 or 1) from the first
/// byte of the provided [`Message`].
impl<L: Decodable, R: Decodable> Decodable for Either<L, R> {
    fn decode(message: &Message) -> Result<Self, OakError> {
        match message.bytes.get(0) {
            // Left variant == 0.
            Some(0) => {
                let inner_message = Message {
                    bytes: message.bytes[1..].to_vec(),
                    handles: message.handles.clone(),
                };
                Ok(Either::Left(L::decode(&inner_message)?))
            }
            // Right variant == 1.
            Some(1) => {
                let inner_message = Message {
                    bytes: message.bytes[1..].to_vec(),
                    handles: message.handles.clone(),
                };
                Ok(Either::Right(R::decode(&inner_message)?))
            }
            // Invalid variant, or not enough bytes.
            _ => Err(OakStatus::ErrInvalidArgs.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn either_round_trip() {
        type T = Either<u32, u32>;

        {
            // This test case is just a baseline reference for the ones below, to spell out the
            // protobuf encoding of the inner object.
            let original = 1988;
            let encoded = original.encode().unwrap();
            assert_eq!(
                Message {
                    bytes: vec![8, 196, 15],
                    handles: vec![]
                },
                encoded
            );
            let decoded = u32::decode(&encoded).unwrap();
            assert_eq!(original, decoded);
        }

        {
            let original = T::Left(1988);
            let encoded = original.encode().unwrap();
            // Note the first byte corresponds to the variant == 0.
            assert_eq!(
                Message {
                    bytes: vec![0, 8, 196, 15],
                    handles: vec![]
                },
                encoded
            );
            let decoded = T::decode(&encoded).unwrap();
            assert_eq!(original, decoded);
        }

        {
            let original = T::Right(1988);
            let encoded = original.encode().unwrap();
            // Note the first byte corresponds to the variant == 1.
            assert_eq!(
                Message {
                    bytes: vec![1, 8, 196, 15],
                    handles: vec![]
                },
                encoded
            );
            let decoded = T::decode(&encoded).unwrap();
            assert_eq!(original, decoded);
        }

        {
            let invalid_variant = 42;
            let encoded_invalid = Message {
                bytes: vec![invalid_variant, 8, 196, 15],
                handles: vec![],
            };
            assert_matches!(
                T::decode(&encoded_invalid),
                Err(OakError::OakStatus(OakStatus::ErrInvalidArgs))
            );
        }
    }
}
