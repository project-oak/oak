use crate::{handle::HandleVisit, Decodable, Encodable, Receiver, Sender};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

impl<T: Encodable + Decodable + HandleVisit> Serialize for Receiver<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_unit()
    }
}

impl<'de, T: Encodable + Decodable + HandleVisit> Deserialize<'de> for Receiver<T> {
    fn deserialize<D: Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        Ok(Receiver::default())
    }
}

impl<T: Encodable + Decodable + HandleVisit> Serialize for Sender<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_unit()
    }
}

impl<'de, T: Encodable + Decodable + HandleVisit> Deserialize<'de> for Sender<T> {
    fn deserialize<D: Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        Ok(Sender::default())
    }
}
