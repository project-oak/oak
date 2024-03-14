//
// Copyright 2021 The Project Oak Authors
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

use anyhow::anyhow;
use bytes::BytesMut;
use oak_proto_rust::oak::oak_functions::lookup_data::Entry;
use prost::Message;
use rand::Rng;

fn create_bytes<R: Rng>(rng: &mut R, size_bytes: usize) -> Vec<u8> {
    let mut buf = vec![0u8; size_bytes];
    rng.fill(buf.as_mut_slice());
    buf
}

fn create_random_entry<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
) -> Entry {
    Entry {
        key: create_bytes(rng, key_size_bytes),
        value: create_bytes(rng, value_size_bytes),
    }
}

/// Generates random lookup entries with the specified sizes for keys and values and serializes it
/// to bytes.
pub fn generate_and_serialize_random_entries<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
    entries: usize,
) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    for _ in 0..entries {
        let entry = create_random_entry(rng, key_size_bytes, value_size_bytes);
        entry
            .encode_length_delimited(&mut buf)
            .map_err(|err| anyhow!("couldn't encode entry: {err}"))?;
    }
    Ok(buf)
}
