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
        Ok(String::from_utf8(message.bytes.clone())
            .map(DummyData)
            .expect("Failed to decode DummyData"))
    }
}
