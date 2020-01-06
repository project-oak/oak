use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum Msg {
    Join(oak::WriteHandle),
    // TODO: Embed native Message struct here when we support proto serialization via Serde.
    // See https://github.com/stepancheg/rust-protobuf#serde_derive-support
    SendMessage(Vec<u8>),
}

// TODO(#389): Automatically generate this code.
//
// Currently we use [bincode](https://github.com/servo/bincode) to serialize data together with a
// tag that allows to reconstruct the enum variant on the other side. We then send the tag+data as
// bytes, and separately we send the handles, which we have to manually re-assemble on the other
// side.
//
// FIDL implements something similar to this in
// https://fuchsia.googlesource.com/fuchsia/+/refs/heads/master/garnet/public/lib/fidl/rust/fidl/src/encoding.rs.
impl crate::Encodable for Msg {
    fn encode(&self) -> Result<(Vec<u8>, Vec<oak::Handle>)> {
        let bytes = bincode::serialize(self).context("could not serialize message to bincode")?;
        // Serialize handles separately.
        let handles = match self {
            Msg::Join(h) => vec![h.handle],
            Msg::SendMessage(_) => vec![],
        };
        Ok((bytes, handles))
    }
}

// TODO(#389): Automatically generate this code.
impl crate::Decodable for Msg {
    fn decode(bytes: &[u8], handles: &[oak::Handle]) -> Result<Self> {
        let msg: Msg =
            bincode::deserialize(&bytes).context("could not deserialize message from bincode")?;
        // Restore handles in the received message.
        let msg = match msg {
            Msg::Join(_) => Msg::Join(oak::WriteHandle { handle: handles[0] }),
            Msg::SendMessage(message_bytes) => Msg::SendMessage(message_bytes),
        };
        Ok(msg)
    }
}
