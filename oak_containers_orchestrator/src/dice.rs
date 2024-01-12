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

use anyhow::Context;
use ciborium::Value;
use coset::cwt::ClaimName;
use oak_dice::cert::{
    CONTAINER_IMAGE_ID, LAYER_3_CODE_MEASUREMENT_ID, LAYER_3_CONFIG_MEASUREMENT_ID, SHA2_256_ID,
};
use oak_remote_attestation::{dice::DiceBuilder, proto::oak::attestation::v1::DiceData};
use prost::Message;
use sha2::{Digest, Sha256};
use std::{
    fs::OpenOptions,
    io::{Read, Seek, Write},
};
use zeroize::Zeroize;

/// The path to the file where the DICE data provided by Stage 1 is stored.
const STAGE1_DICE_DATA_PATH: &str = "/oak/dice";

/// Loads the DICE data from the file provided by Stage 1.
///
/// The file is also overwritten with zeros to ensure it cannot be reused by another process.
pub fn load_stage1_dice_data() -> anyhow::Result<DiceBuilder> {
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(STAGE1_DICE_DATA_PATH)
        .context("couldn't open DICE data file")?;
    let size = file.metadata().map(|m| m.len() as usize).unwrap_or(0);

    let mut buffer = Vec::with_capacity(size);
    file.read_to_end(&mut buffer)
        .context("couldn't read DICE data from file")?;

    let result =
        DiceData::decode_length_delimited(&buffer[..]).context("couldn't parse DICE data")?;

    buffer.zeroize();
    file.rewind()?;
    file.write_all(&buffer)
        .context("couldn't overwrite DICE data file")?;
    result.try_into()
}

/// Measures the downloaded container image bytes and configuration and returns these as a vector of
/// additional CWT claims.
pub fn measure_container_and_config(
    container_bytes: &[u8],
    config_bytes: &[u8],
) -> Vec<(ClaimName, Value)> {
    let mut container_digest = Sha256::default();
    container_digest.update(container_bytes);
    let container_digest = container_digest.finalize();
    let mut config_digest = Sha256::default();
    config_digest.update(config_bytes);
    let config_digest = config_digest.finalize();
    vec![(
        ClaimName::PrivateUse(CONTAINER_IMAGE_ID),
        Value::Map(vec![
            (
                Value::Integer(LAYER_3_CODE_MEASUREMENT_ID.into()),
                Value::Map(vec![(
                    Value::Integer(SHA2_256_ID.into()),
                    Value::Bytes(container_digest[..].to_vec()),
                )]),
            ),
            (
                Value::Integer(LAYER_3_CONFIG_MEASUREMENT_ID.into()),
                Value::Map(vec![(
                    Value::Integer(SHA2_256_ID.into()),
                    Value::Bytes(config_digest[..].to_vec()),
                )]),
            ),
        ]),
    )]
}
