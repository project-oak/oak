//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Context;
use oak_proto_rust::oak::attestation::v1::Event;
use prost::Message;
use prost_types::Any;

/// Decodes a serialized event into a specified [`Message`].
pub fn decode_event_proto<M: Message + Default>(
    expected_type_url: &str,
    encoded_event: &[u8],
) -> anyhow::Result<M> {
    let event_proto = Event::decode(encoded_event)
        .map_err(|error| anyhow::anyhow!("failed to decode event: {}", error))?;
    decode_protobuf_any::<M>(
        expected_type_url,
        event_proto.event.as_ref().context("no event found in the `event` field")?,
    )
}

/// Decodes [`Any`] message into a specified [`Message`].
pub fn decode_protobuf_any<M: Message + Default>(
    expected_type_url: &str,
    message: &Any,
) -> anyhow::Result<M> {
    if message.type_url.as_str() != expected_type_url {
        anyhow::bail!(
            "expected message with type url: {}, found: {}",
            expected_type_url,
            message.type_url.as_str()
        );
    }
    M::decode(message.value.as_ref()).map_err(|error| {
        anyhow::anyhow!(
            "couldn't decode `google.protobuf.Any` message into {}: {:?}",
            expected_type_url,
            error
        )
    })
}
