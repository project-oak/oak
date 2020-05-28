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

use crate::error::Error;

/// An unsigned 32-bit value (key) that maps to a byte-string (value).
#[derive(Debug, PartialEq, Eq, PartialOrd, Hash, Clone, Copy)]
pub enum Tag {
    // Enforcement of the "tags in strictly increasing order" rule is done using the
    // little-endian encoding of the ASCII tag value; e.g. 'SIG\x00' is 0x00474953 and
    // 'NONC' is 0x434e4f4e.
    //
    // Tags are written here in ascending order
    SIG,
    NONC,
    DELE,
    PATH,
    RADI,
    PUBK,
    MIDP,
    SREP,
    MINT,
    ROOT,
    CERT,
    MAXT,
    INDX,
    PAD,
}

impl Tag {
    /// Translates a tag into its on-the-wire representation
    pub fn wire_value(self) -> &'static [u8] {
        match self {
            Tag::CERT => b"CERT",
            Tag::DELE => b"DELE",
            Tag::INDX => b"INDX",
            Tag::MAXT => b"MAXT",
            Tag::MIDP => b"MIDP",
            Tag::MINT => b"MINT",
            Tag::NONC => b"NONC",
            Tag::PAD => b"PAD\xff",
            Tag::PATH => b"PATH",
            Tag::PUBK => b"PUBK",
            Tag::RADI => b"RADI",
            Tag::ROOT => b"ROOT",
            Tag::SIG => b"SIG\x00",
            Tag::SREP => b"SREP",
        }
    }

    /// Return the `Tag` corresponding to the on-the-wire representation in `bytes` or an
    /// `Error::InvalidTag` if `bytes` do not correspond to a valid tag.
    pub fn from_wire(bytes: &[u8]) -> Result<Self, Error> {
        match bytes {
            b"CERT" => Ok(Tag::CERT),
            b"DELE" => Ok(Tag::DELE),
            b"INDX" => Ok(Tag::INDX),
            b"MAXT" => Ok(Tag::MAXT),
            b"MIDP" => Ok(Tag::MIDP),
            b"MINT" => Ok(Tag::MINT),
            b"NONC" => Ok(Tag::NONC),
            b"PAD\xff" => Ok(Tag::PAD),
            b"PATH" => Ok(Tag::PATH),
            b"PUBK" => Ok(Tag::PUBK),
            b"RADI" => Ok(Tag::RADI),
            b"ROOT" => Ok(Tag::ROOT),
            b"SIG\x00" => Ok(Tag::SIG),
            b"SREP" => Ok(Tag::SREP),
            _ => Err(Error::InvalidTag(Box::from(bytes))),
        }
    }
}
