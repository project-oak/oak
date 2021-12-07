use std::fmt;

use kstring::KString;
use serde::ser::Impossible;
use serde::{self, Serialize};

use crate::model::value::ser::ValueSerializer;
use crate::model::Object;
use crate::model::{Value, ValueView};

#[derive(Debug)]
pub(crate) struct SerError(crate::error::Error);

impl SerError {
    pub(crate) fn new(e: crate::error::Error) -> Self {
        Self(e)
    }

    // Somehow `From` breaks `liquid-derive`.
    pub(crate) fn into(self) -> crate::error::Error {
        self.0
    }

    pub(crate) fn unknown_type(unexpected: &dyn ValueView) -> Self {
        crate::error::Error::with_msg(format!("Unknown type: {}", unexpected.type_name())).into()
    }

    pub(crate) fn invalid_type(unexpected: &dyn ValueView, expected: &str) -> Self {
        crate::error::Error::with_msg(format!(
            "Invalid type: {}, expected {}",
            unexpected.type_name(),
            expected
        ))
        .into()
    }
}

impl fmt::Display for SerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.0)
    }
}

impl ::std::error::Error for SerError {
    fn source(&self) -> Option<&(dyn (::std::error::Error) + 'static)> {
        ::std::error::Error::source(&self.0)
    }
}

impl serde::ser::Error for SerError {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        SerError(crate::error::Error::with_msg(format!("{}", msg)))
    }
}

impl serde::de::Error for SerError {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        SerError(crate::error::Error::with_msg(format!("{}", msg)))
    }
}

impl From<crate::error::Error> for SerError {
    fn from(e: crate::error::Error) -> Self {
        SerError::new(e)
    }
}

pub(crate) struct SerializeStructVariant<O> {
    pub(crate) name: KString,
    pub(crate) map: Object,
    pub(crate) other: std::marker::PhantomData<O>,
}

impl<O: From<Object>> serde::ser::SerializeStructVariant for SerializeStructVariant<O> {
    type Ok = O;
    type Error = SerError;

    fn serialize_field<T: ?Sized>(&mut self, key: &'static str, value: &T) -> Result<(), SerError>
    where
        T: Serialize,
    {
        self.map
            .insert(KString::from_static(key), value.serialize(ValueSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<O, SerError> {
        let mut object = Object::new();

        object.insert(self.name, Value::Object(self.map));

        Ok(From::from(object))
    }
}

pub(crate) struct SerializeTupleVariant<O> {
    pub(crate) name: KString,
    pub(crate) vec: Vec<Value>,
    pub(crate) other: std::marker::PhantomData<O>,
}

impl<O: From<Object>> serde::ser::SerializeTupleVariant for SerializeTupleVariant<O> {
    type Ok = O;
    type Error = SerError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), SerError>
    where
        T: Serialize,
    {
        self.vec.push(value.serialize(ValueSerializer)?);
        Ok(())
    }

    fn end(self) -> Result<O, SerError> {
        let mut object = Object::new();

        object.insert(self.name, Value::Array(self.vec));

        Ok(From::from(object))
    }
}

pub(crate) enum SerializeMap<O> {
    Map {
        map: Object,
        next_key: Option<KString>,
        other: std::marker::PhantomData<O>,
    },
}

impl<O: From<Object>> serde::ser::SerializeStruct for SerializeMap<O> {
    type Ok = O;
    type Error = SerError;

    fn serialize_field<T: ?Sized>(&mut self, key: &'static str, value: &T) -> Result<(), SerError>
    where
        T: Serialize,
    {
        match *self {
            SerializeMap::Map {
                ref mut next_key, ..
            } => {
                *next_key = Some(KString::from_static(key));
                serde::ser::SerializeMap::serialize_value(self, value)
            }
        }
    }

    fn end(self) -> Result<O, SerError> {
        match self {
            SerializeMap::Map { .. } => serde::ser::SerializeMap::end(self),
        }
    }
}

impl<O: From<Object>> serde::ser::SerializeMap for SerializeMap<O> {
    type Ok = O;
    type Error = SerError;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), SerError>
    where
        T: Serialize,
    {
        match *self {
            SerializeMap::Map {
                ref mut next_key, ..
            } => {
                *next_key = Some(key.serialize(MapKeySerializer)?);
                Ok(())
            }
        }
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), SerError>
    where
        T: Serialize,
    {
        match *self {
            SerializeMap::Map {
                ref mut map,
                ref mut next_key,
                ..
            } => {
                let key = next_key.take();
                // Panic because this indicates a bug in the program rather than an
                // expected failure.
                let key = key.expect("serialize_value called before serialize_key");
                map.insert(key, value.serialize(ValueSerializer)?);
                Ok(())
            }
        }
    }

    fn end(self) -> Result<O, SerError> {
        match self {
            SerializeMap::Map { map, .. } => Ok(From::from(map)),
        }
    }
}

struct MapKeySerializer;

fn key_must_be_a_string() -> SerError {
    SerError::new(crate::error::Error::with_msg("Key must be a string."))
}

impl serde::Serializer for MapKeySerializer {
    type Ok = KString;
    type Error = SerError;

    type SerializeSeq = Impossible<KString, SerError>;
    type SerializeTuple = Impossible<KString, SerError>;
    type SerializeTupleStruct = Impossible<KString, SerError>;
    type SerializeTupleVariant = Impossible<KString, SerError>;
    type SerializeMap = Impossible<KString, SerError>;
    type SerializeStruct = Impossible<KString, SerError>;
    type SerializeStructVariant = Impossible<KString, SerError>;

    #[inline]
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(KString::from_static(variant))
    }

    #[inline]
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        value.serialize(self)
    }

    fn serialize_bool(self, _value: bool) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_i8(self, value: i8) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_i16(self, value: i16) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_i32(self, value: i32) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_i64(self, value: i64) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_u8(self, value: u8) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_u16(self, value: u16) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_u32(self, value: u32) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_u64(self, value: u64) -> Result<Self::Ok, Self::Error> {
        Ok(value.to_string().into())
    }

    fn serialize_f32(self, _value: f32) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_f64(self, _value: f64) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    #[inline]
    fn serialize_char(self, value: char) -> Result<Self::Ok, Self::Error> {
        Ok({
            let mut s = String::new();
            s.push(value);
            s.into()
        })
    }

    #[inline]
    fn serialize_str(self, value: &str) -> Result<Self::Ok, Self::Error> {
        Ok(KString::from_ref(value))
    }

    fn serialize_bytes(self, _value: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(key_must_be_a_string())
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_some<T: ?Sized>(self, _value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(key_must_be_a_string())
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err(key_must_be_a_string())
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err(key_must_be_a_string())
    }
}
