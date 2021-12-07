use kstring::KString;
use serde::ser::Impossible;
use serde::{self, Serialize};

use crate::model::ser::SerError;
use crate::model::Scalar;

/// Convert a `T` into `liquid_core::model::Scalar`.
///
/// # Examples
///
/// ```rust
/// let s = "foo";
/// let value = liquid_core::model::to_scalar(&s).unwrap();
/// assert_eq!(value, liquid_core::model::Scalar::new(s));
/// ```
pub fn to_scalar<T>(value: &T) -> Result<Scalar, crate::error::Error>
where
    T: Serialize,
{
    value.serialize(ScalarSerializer).map_err(|e| e.into())
}

pub(crate) struct ScalarSerializer;

fn scalar_must_be_a_string() -> SerError {
    SerError::new(crate::error::Error::with_msg("Scalar must be a string."))
}

impl serde::Serializer for ScalarSerializer {
    type Ok = Scalar;
    type Error = SerError;

    type SerializeSeq = Impossible<Scalar, SerError>;
    type SerializeTuple = Impossible<Scalar, SerError>;
    type SerializeTupleStruct = Impossible<Scalar, SerError>;
    type SerializeTupleVariant = Impossible<Scalar, SerError>;
    type SerializeMap = Impossible<Scalar, SerError>;
    type SerializeStruct = Impossible<Scalar, SerError>;
    type SerializeStructVariant = Impossible<Scalar, SerError>;

    #[inline]
    fn serialize_bool(self, value: bool) -> Result<Scalar, SerError> {
        Ok(Scalar::new(value))
    }

    #[inline]
    fn serialize_i8(self, value: i8) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_i16(self, value: i16) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_i32(self, value: i32) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    fn serialize_i64(self, value: i64) -> Result<Scalar, SerError> {
        Ok(Scalar::new(value))
    }

    #[inline]
    fn serialize_u8(self, value: u8) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_u16(self, value: u16) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_u32(self, value: u32) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_u64(self, value: u64) -> Result<Scalar, SerError> {
        serialize_as_i64(value)
    }

    #[inline]
    fn serialize_f32(self, value: f32) -> Result<Scalar, SerError> {
        self.serialize_f64(f64::from(value))
    }

    #[inline]
    fn serialize_f64(self, value: f64) -> Result<Scalar, SerError> {
        Ok(Scalar::new(value))
    }

    #[inline]
    fn serialize_char(self, value: char) -> Result<Scalar, SerError> {
        let mut s = String::new();
        s.push(value);
        self.serialize_str(&s)
    }

    #[inline]
    fn serialize_str(self, value: &str) -> Result<Scalar, SerError> {
        Ok(Scalar::new(KString::from_ref(value)))
    }

    fn serialize_bytes(self, _value: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Scalar, SerError> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Scalar, SerError>
    where
        T: Serialize,
    {
        value.serialize(ScalarSerializer)
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
        Err(scalar_must_be_a_string())
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_some<T: ?Sized>(self, _value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(scalar_must_be_a_string())
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err(scalar_must_be_a_string())
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err(scalar_must_be_a_string())
    }
}

#[inline]
fn serialize_as_i64<T: num_traits::cast::NumCast>(value: T) -> Result<Scalar, SerError> {
    let value = num_traits::cast::cast::<T, i64>(value)
        .ok_or_else(|| SerError::new(crate::error::Error::with_msg("Cannot fit number")))?;
    Ok(Scalar::new(value))
}
