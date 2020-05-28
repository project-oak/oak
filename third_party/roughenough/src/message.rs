// Copyright 2017-2019 int08h LLC
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

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::{
    collections::HashMap,
    io::{Cursor, Read, Write},
    iter::once,
};

use crate::{error::Error, tag::Tag};

///
/// A Roughtime protocol message; a map of u32 tags to arbitrary byte-strings.
#[derive(Debug, Clone)]
pub struct RtMessage {
    tags: Vec<Tag>,
    values: Vec<Vec<u8>>,
}

impl RtMessage {
    /// Construct a new RtMessage
    ///
    /// ## Arguments
    ///
    /// * `num_fields` - Reserve space for this many fields.
    pub fn new(num_fields: u32) -> Self {
        RtMessage {
            tags: Vec::with_capacity(num_fields as usize),
            values: Vec::with_capacity(num_fields as usize),
        }
    }

    /// Construct a new RtMessage from the on-the-wire representation in `bytes`
    ///
    /// ## Arguments
    ///
    /// * `bytes` - On-the-wire representation
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let bytes_len = bytes.len();

        if bytes_len < 4 {
            return Err(Error::MessageTooShort);
        } else if bytes_len % 4 != 0 {
            return Err(Error::InvalidAlignment(bytes_len as u32));
        }

        let mut msg = Cursor::new(bytes);
        let num_tags = msg.read_u32::<LittleEndian>()?;

        match num_tags {
            0 => Ok(RtMessage::new(0)),
            1 => RtMessage::single_tag_message(bytes, &mut msg),
            2..=1024 => RtMessage::multi_tag_message(num_tags, bytes, &mut msg),
            _ => Err(Error::InvalidNumTags(num_tags)),
        }
    }

    ///
    /// Dangerous: construct a new RtMessage **without validation or error checking**.
    ///
    /// Intended _only_ for construction of deliberately bogus responses as part of [Roughtime's
    /// ecosystem](https://roughtime.googlesource.com/roughtime/+/HEAD/ECOSYSTEM.md#maintaining-a-healthy-software-ecosystem).
    pub fn new_deliberately_invalid(tags: Vec<Tag>, values: Vec<Vec<u8>>) -> Self {
        RtMessage { tags, values }
    }

    /// Internal function to create a single tag message
    fn single_tag_message(bytes: &[u8], msg: &mut Cursor<&[u8]>) -> Result<Self, Error> {
        if bytes.len() < 8 {
            return Err(Error::MessageTooShort);
        }

        let pos = msg.position() as usize;
        msg.set_position((pos + 4) as u64);

        let mut value = Vec::new();
        msg.read_to_end(&mut value)?;

        let tag = Tag::from_wire(&bytes[pos..pos + 4])?;
        let mut rt_msg = RtMessage::new(1);
        rt_msg.add_field(tag, &value)?;

        Ok(rt_msg)
    }

    /// Internal function to create a multiple tag message
    fn multi_tag_message(
        num_tags: u32,
        bytes: &[u8],
        msg: &mut Cursor<&[u8]>,
    ) -> Result<Self, Error> {
        let bytes_len = bytes.len();
        let mut offsets = Vec::with_capacity((num_tags - 1) as usize);

        for _ in 0..num_tags - 1 {
            let offset = msg.read_u32::<LittleEndian>()?;

            if offset % 4 != 0 {
                return Err(Error::InvalidAlignment(offset));
            } else if offset > bytes_len as u32 {
                return Err(Error::InvalidOffsetValue(offset));
            }

            offsets.push(offset as usize);
        }

        let mut buf = [0; 4];
        let mut tags = Vec::with_capacity(num_tags as usize);

        for _ in 0..num_tags {
            if msg.read_exact(&mut buf).is_err() {
                return Err(Error::MessageTooShort);
            }

            let tag = Tag::from_wire(&buf)?;

            if let Some(last_tag) = tags.last() {
                if tag <= *last_tag {
                    return Err(Error::TagNotStrictlyIncreasing(tag));
                }
            }

            tags.push(tag);
        }

        // All offsets are relative to the end of the header,
        // which is our current position
        let header_end = msg.position() as usize;

        // Compute the end of the last value,
        // as an offset from the end of the header
        let msg_end = bytes.len() - header_end;

        let mut rt_msg = RtMessage::new(num_tags);

        for (tag, (value_start, value_end)) in tags.into_iter().zip(
            once(&0)
                .chain(offsets.iter())
                .zip(offsets.iter().chain(once(&msg_end))),
        ) {
            let start_idx = header_end + value_start;
            let end_idx = header_end + value_end;

            if end_idx > bytes_len || start_idx > end_idx {
                return Err(Error::InvalidValueLength(tag, end_idx as u32));
            }

            let value = bytes[start_idx..end_idx].to_vec();
            rt_msg.add_field(tag, &value)?;
        }

        Ok(rt_msg)
    }

    /// Add a field to this `RtMessage`
    ///
    /// ## Arguments
    ///
    /// * `tag` - The `Tag` to add. Tags must be added in **strictly increasing order**, violating
    ///   this will result in a `Error::TagNotStrictlyIncreasing`.
    ///
    /// * `value` - Value for the tag.
    pub fn add_field(&mut self, tag: Tag, value: &[u8]) -> Result<(), Error> {
        if let Some(last_tag) = self.tags.last() {
            if tag <= *last_tag {
                return Err(Error::TagNotStrictlyIncreasing(tag));
            }
        }

        self.tags.push(tag);
        self.values.push(value.to_vec());

        Ok(())
    }

    /// Retrieve the value associated with `tag`, if present.
    ///
    /// ## Arguments
    ///
    /// * `tag` - The `Tag` to try and retrieve.
    pub fn get_field(&self, tag: Tag) -> Option<&[u8]> {
        for (i, self_tag) in self.tags.iter().enumerate() {
            if tag == *self_tag {
                return Some(&self.values[i]);
            }
        }

        None
    }

    /// Returns the number of tag/value pairs in the message
    pub fn num_fields(&self) -> u32 {
        self.tags.len() as u32
    }

    /// Returns a slice of the tags in the message
    pub fn tags(&self) -> &[Tag] {
        &self.tags
    }

    /// Returns a slice of the values in the message
    pub fn values(&self) -> &[Vec<u8>] {
        &self.values
    }

    /// Converts the message into a `HashMap` mapping each tag to its value
    pub fn into_hash_map(self) -> HashMap<Tag, Vec<u8>> {
        self.tags.into_iter().zip(self.values.into_iter()).collect()
    }

    /// Encode this message into its on-the-wire representation.
    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        let num_tags = self.tags.len();
        let mut out = Vec::with_capacity(self.encoded_size());

        // number of tags
        out.write_u32::<LittleEndian>(num_tags as u32)?;

        // offset(s) to values, IFF there are two or more tags
        if num_tags > 1 {
            let mut offset_sum = self.values[0].len();

            for val in &self.values[1..] {
                out.write_u32::<LittleEndian>(offset_sum as u32)?;
                offset_sum += val.len();
            }
        }

        // write tags
        for tag in &self.tags {
            out.write_all(tag.wire_value())?;
        }

        // write values
        for value in &self.values {
            out.write_all(value)?;
        }

        // check we wrote exactly what we expected
        assert_eq!(out.len(), self.encoded_size(), "unexpected length");

        Ok(out)
    }

    /// Returns the length in bytes of this message's on-the-wire representation.
    pub fn encoded_size(&self) -> usize {
        let num_tags = self.tags.len();
        let tags_size = 4 * num_tags;
        let offsets_size = if num_tags < 2 { 0 } else { 4 * (num_tags - 1) };
        let values_size: usize = self.values.iter().map(|v| v.len()).sum();

        4 + tags_size + offsets_size + values_size
    }

    /// Adds a PAD tag to the end of this message, with a length
    /// set such that the final encoded size of this message is 1KB
    ///
    /// If the encoded size of this message is already >= 1KB,
    /// this method does nothing
    pub fn pad_to_kilobyte(&mut self) {
        let size = self.encoded_size();
        if size >= 1024 {
            return;
        }

        let mut padding_needed = 1024 - size;
        if self.tags.len() == 1 {
            // If we currently only have one tag, adding a padding tag will cause
            // a 32-bit offset values to be written
            padding_needed -= 4;
        }
        padding_needed -= Tag::PAD.wire_value().len();
        let padding = vec![0; padding_needed];

        self.add_field(Tag::PAD, &padding).unwrap();

        assert_eq!(self.encoded_size(), 1024);
    }
}

#[cfg(test)]
mod test {
    use crate::{message::*, tag::Tag};
    use byteorder::{LittleEndian, ReadBytesExt};
    use std::io::{Cursor, Read};

    #[test]
    fn empty_message_size() {
        let msg = RtMessage::new(0);

        assert_eq!(msg.num_fields(), 0);
        // Empty message is 4 bytes, a single num_tags value
        assert_eq!(msg.encoded_size(), 4);
    }

    #[test]
    fn single_field_message_size() {
        let mut msg = RtMessage::new(1);
        msg.add_field(Tag::NONC, b"1234").unwrap();

        assert_eq!(msg.num_fields(), 1);
        // Single tag message is 4 (num_tags) + 4 (NONC) + 4 (value)
        assert_eq!(msg.encoded_size(), 12);
    }

    #[test]
    fn two_field_message_size() {
        let mut msg = RtMessage::new(2);
        msg.add_field(Tag::NONC, b"1234").unwrap();
        msg.add_field(Tag::PAD, b"abcd").unwrap();

        assert_eq!(msg.num_fields(), 2);
        // Two tag message
        //   4 num_tags
        //   8 (NONC, PAD) tags
        //   4 PAD offset
        //   8 values
        assert_eq!(msg.encoded_size(), 24);
    }

    #[test]
    fn empty_message_encoding() {
        let msg = RtMessage::new(0);
        let mut encoded = Cursor::new(msg.encode().unwrap());

        assert_eq!(encoded.read_u32::<LittleEndian>().unwrap(), 0);
    }

    #[test]
    fn single_field_message_encoding() {
        let value = vec![b'a'; 64];
        let mut msg = RtMessage::new(1);

        msg.add_field(Tag::CERT, &value).unwrap();

        let mut encoded = Cursor::new(msg.encode().unwrap());

        // num tags
        assert_eq!(encoded.read_u32::<LittleEndian>().unwrap(), 1);

        // CERT tag
        let mut cert = [0u8; 4];
        encoded.read_exact(&mut cert).unwrap();
        assert_eq!(cert, Tag::CERT.wire_value());

        // CERT value
        let mut read_val = vec![0u8; 64];
        encoded.read_exact(&mut read_val).unwrap();
        assert_eq!(value, read_val);

        // Entire message was read
        assert_eq!(encoded.position(), 72);

        // Round-trip single-tag message
        RtMessage::from_bytes(&msg.encode().unwrap()).unwrap();
    }

    #[test]
    fn two_field_message_encoding() {
        let dele_value = vec![b'a'; 24];
        let maxt_value = vec![b'z'; 32];

        let mut msg = RtMessage::new(2);
        msg.add_field(Tag::DELE, &dele_value).unwrap();
        msg.add_field(Tag::MAXT, &maxt_value).unwrap();

        let mut encoded = Cursor::new(msg.encode().unwrap());
        // Wire encoding
        //   4 num_tags
        //   8 (DELE, MAXT) tags
        //   4 MAXT offset
        //  24 DELE value
        //  32 MAXT value

        // num tags
        assert_eq!(encoded.read_u32::<LittleEndian>().unwrap(), 2);

        // Offset past DELE value to start of MAXT value
        assert_eq!(
            encoded.read_u32::<LittleEndian>().unwrap(),
            dele_value.len() as u32
        );

        // DELE tag
        let mut dele = [0u8; 4];
        encoded.read_exact(&mut dele).unwrap();
        assert_eq!(dele, Tag::DELE.wire_value());

        // MAXT tag
        let mut maxt = [0u8; 4];
        encoded.read_exact(&mut maxt).unwrap();
        assert_eq!(maxt, Tag::MAXT.wire_value());

        // DELE value
        let mut read_dele_val = vec![0u8; 24];
        encoded.read_exact(&mut read_dele_val).unwrap();
        assert_eq!(dele_value, read_dele_val);

        // MAXT value
        let mut read_maxt_val = vec![0u8; 32];
        encoded.read_exact(&mut read_maxt_val).unwrap();
        assert_eq!(maxt_value, read_maxt_val);

        // Everything was read
        assert_eq!(encoded.position() as usize, msg.encoded_size());

        // Round-trip multi-tag message
        RtMessage::from_bytes(&msg.encode().unwrap()).unwrap();
    }

    #[test]
    fn from_bytes_zero_tags() {
        let bytes = [0, 0, 0, 0];
        let msg = RtMessage::from_bytes(&bytes).unwrap();

        assert_eq!(msg.num_fields(), 0);
    }

    #[test]
    fn retrieve_message_values() {
        let val1 = b"aabbccddeeffgg";
        let val2 = b"0987654321";

        let mut msg = RtMessage::new(2);
        msg.add_field(Tag::NONC, val1).unwrap();
        msg.add_field(Tag::MAXT, val2).unwrap();

        assert_eq!(msg.get_field(Tag::NONC), Some(val1.as_ref()));
        assert_eq!(msg.get_field(Tag::MAXT), Some(val2.as_ref()));
        assert_eq!(msg.get_field(Tag::CERT), None);
    }

    #[test]
    #[should_panic(expected = "InvalidAlignment")]
    fn from_bytes_offset_past_end_of_message() {
        let mut msg = RtMessage::new(2);
        msg.add_field(Tag::NONC, b"1111").unwrap();
        msg.add_field(Tag::PAD, b"aaaaaaaaa").unwrap();

        let mut bytes = msg.encode().unwrap();
        // set the PAD value offset to beyond end of the message
        bytes[4] = 128;

        RtMessage::from_bytes(&bytes).unwrap();
    }

    #[test]
    #[should_panic(expected = "InvalidAlignment")]
    fn from_bytes_too_few_bytes_for_tags() {
        // Header says two tags (8 bytes) but truncate first tag at 2 bytes
        let bytes = &[0x02, 0, 0, 0, 4, 0, 0, 0, 0, 0];
        RtMessage::from_bytes(bytes).unwrap();
    }
}
