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

use std::io::copy;
use tonic::codec::{Codec, DecodeBuf, Decoder, EncodeBuf, Encoder};

/// Encapsulates [`VecEncoder`] and [`VecDecoder`] types and is used by [`tonic::server::Grpc`].
#[derive(Default)]
pub struct VecCodec;

impl Codec for VecCodec {
    type Encode = Vec<u8>;
    type Decode = Vec<u8>;

    type Encoder = VecEncoder;
    type Decoder = VecDecoder;

    fn encoder(&mut self) -> Self::Encoder {
        VecEncoder::default()
    }

    fn decoder(&mut self) -> Self::Decoder {
        VecDecoder::default()
    }
}

/// Custom encoder for creating [`tonic::codec::EncodeBuf`] from bytes.
#[derive(Default)]
pub struct VecEncoder;

impl Encoder for VecEncoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn encode(&mut self, item: Self::Item, dst: &mut EncodeBuf<'_>) -> Result<(), Self::Error> {
        use bytes::BufMut;

        dst.put(item.as_ref());
        Ok(())
    }
}

/// Custom decoder for extracting bytes from [`tonic::codec::DecodeBuf`].
#[derive(Default)]
pub struct VecDecoder;

impl Decoder for VecDecoder {
    type Item = Vec<u8>;
    type Error = tonic::Status;

    fn decode(&mut self, src: &mut DecodeBuf<'_>) -> Result<Option<Self::Item>, Self::Error> {
        use bytes::buf::BufExt;

        let mut item = vec![];
        copy(&mut src.reader(), &mut item).expect("Couldn't copy from buffer");
        Ok(Some(item))
    }
}
