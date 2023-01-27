//
// Copyright 2023 The Project Oak Authors
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

use alloc::{vec, vec::Vec};
use anyhow::anyhow;
use core::cmp::Ordering;

pub(crate) fn xor<const L: usize>(first: &[u8; L], second: &[u8; L]) -> [u8; L] {
    let mut result = [0u8; L];
    for i in 0..result.len() {
        result[i] = first[i] ^ second[i];
    }
    result
}

/// Converts a nonnegative integer to an octet string of a specified length.
/// <https://www.rfc-editor.org/rfc/rfc8017.html#section-4.1>
pub(crate) fn i2osp<const L: usize>(value: u128) -> anyhow::Result<[u8; L]> {
    let encoded_value: Vec<u8> = value
        .to_be_bytes()
        .into_iter()
        // Remove leading zeros.
        .skip_while(|&x| x == 0)
        .collect();

    match encoded_value.len().cmp(&L) {
        Ordering::Less => {
            let mut output = vec![0u8; L - encoded_value.len()];
            output.extend_from_slice(&encoded_value);
            output
                .try_into()
                .map_err(|error| anyhow!("couldn't convert into a fixed size array: {:?}", error))
        }
        Ordering::Equal => encoded_value[encoded_value.len() - L..]
            .to_vec()
            .try_into()
            .map_err(|error| anyhow!("couldn't convert into a fixed size array: {:?}", error)),
        Ordering::Greater => Err(anyhow!(
            "too long octet string of {}, maximum expected size length {}",
            encoded_value.len(),
            L
        )),
    }
}
