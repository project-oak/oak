//
// Copyright 2022 The Project Oak Authors
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

//! A browser compatible gRPC web client for unary requests. Manually written,
//! as while a web-compatible port of the tonic gRPC client for exists, it
//! (at the time of writing) is not well maintained and has version conflicts
//! with the newest tonic.

use anyhow::{anyhow, Context};
use bytes::{Buf, BufMut, Bytes, BytesMut};

/// Invoke unary gRPC-web service.
pub async fn grpc_web_unary<A: prost::Message, B: Default + prost::Message>(
    uri: &str,
    message: A,
) -> anyhow::Result<B> {
    let request_bytes = encode_body(message).context("couldn't encode message")?;
    let response_bytes = send(uri, request_bytes)
        .await
        .context("couldn't send message")?;
    let reply = decode_body::<B>(response_bytes)
        .await
        .context("couldn't decode message")?;
    Ok(reply)
}

async fn send(uri: &str, request_bytes: bytes::Bytes) -> anyhow::Result<bytes::Bytes> {
    let client = reqwest::Client::new();
    let response = client
        .post(uri)
        .header(reqwest::header::CONTENT_TYPE, "application/grpc-web")
        // Setting this custom header includes its key in preflight request's
        // `access-control-request-headers` header, marking the preflight
        // request as related to grpc-web.
        // Ref: https://github.com/hyperium/tonic/blob/8084f4ea26cccf9bd2d96d2a81eaea490aaf603b/tonic-web/src/service.rs#L43
        .header("x-grpc-web", "1")
        .body(request_bytes)
        .send()
        .await
        .map_err(|error| anyhow!("couldn't get response {:?}", error))?
        .bytes()
        .await
        .map_err(|error| anyhow!("couldn't get response bytes {:?}", error))?;
    Ok(response)
}

// One byte for the compression flag plus four bytes for the length.
// Ref: https://github.com/grpc/grpc/blob/8558f46d35cedc3ea31787aebf8d9cb07a3fc547/doc/PROTOCOL-HTTP2.md
const GRPC_HEADER_SIZE: usize = 5;

// Based off https://github.com/hyperium/tonic/blob/91b73f9fc3c1bc281e85177808721b3efe37ece0/examples/src/grpc-web/client.rs
fn encode_body<T>(msg: T) -> anyhow::Result<Bytes>
where
    T: prost::Message,
{
    let mut buf = BytesMut::with_capacity(1024);

    // first skip past the header by writing placeholder bytes
    buf.reserve(GRPC_HEADER_SIZE);
    buf.put_bytes(0, GRPC_HEADER_SIZE);

    // write the message
    msg.encode(&mut buf)
        .map_err(|error| anyhow!("couldn't encode message {:?}", error))?;

    // now we know the size of encoded message and can write the
    // header
    let len = buf.len() - GRPC_HEADER_SIZE;
    {
        let mut buf = &mut buf[..GRPC_HEADER_SIZE];

        // compression flag, 0 means "no compression"
        buf.put_u8(0);

        buf.put_u32(len as u32);
    }

    Ok(buf.split_to(len + GRPC_HEADER_SIZE).freeze())
}

// Based off https://github.com/hyperium/tonic/blob/91b73f9fc3c1bc281e85177808721b3efe37ece0/examples/src/grpc-web/client.rs
async fn decode_body<T>(mut body: Bytes) -> anyhow::Result<T>
where
    T: Default + prost::Message,
{
    // ignore the compression flag
    body.advance(1);

    let len = body.get_u32();
    let msg = T::decode(&mut body.split_to(len as usize))
        .map_err(|error| anyhow!("couldn't decode message {:?}", error))?;

    Ok(msg)
}
