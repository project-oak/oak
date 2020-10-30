use oak::{
    handle::HandleVisit,
    io::{Decodable, Encodable, Message},
    OakError,
};
use serde::{Deserialize, Serialize};

pub struct Bincoded<T>(T);

impl<T: Clone + Serialize + HandleVisit> Encodable for Bincoded<T> {
    fn encode(&self) -> Result<Message, OakError> {
        Ok(Message {
            bytes: bincode::serialize(&self.0).map_err(|_| OakError::ProtobufEncodeError(None))?,
            handles: oak::handle::extract_handles(&mut self.0.clone()),
        })
    }
}

impl<'de, T: Clone + Deserialize<'de> + HandleVisit> Decodable for Bincoded<T> {
    fn decode(message: &Message) -> Result<Self, OakError> {
        // Yikes! Need to fix lifetimes
        let clone = Box::leak(Box::new(message.clone()));
        let mut decoded =
            bincode::deserialize(&clone.bytes).map_err(|_| OakError::ProtobufDecodeError(None))?;
        oak::handle::inject_handles(&mut decoded, &message.handles)?;
        Ok(Bincoded(decoded))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oak::io::{Encodable, Receiver};

    #[derive(Clone, Serialize, Deserialize, HandleVisit, Debug, PartialEq)]
    struct Test {
        a: String,
        b: Receiver<()>,
    }

    #[test]
    fn roundtrip() {
        let test = Test {
            a: "Hello, world!".to_string(),
            b: Receiver::new(oak::ReadHandle { handle: 42 }),
        };

        let bincoded = Bincoded(test);
        let msg = bincoded.encode().unwrap();
        let decoded: Bincoded<Test> = Bincoded::decode(&msg).unwrap();

        assert_eq!(decoded.0, bincoded.0);
    }
}
