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

use std::{
    fs::OpenOptions,
    io::{Read, Seek, Write},
};

use anyhow::Context;
#[allow(deprecated)]
use oak_attestation::ApplicationKeysAttester;
use oak_attestation_types::{attester::Attester, util::Serializable};
use zeroize::Zeroize;

/// The path to the file where the DICE data provided by Stage 1 is stored.
const STAGE1_DICE_DATA_PATH: &str = "/oak/dice";

/// Loads the DICE data from the file provided by Stage 1.
///
/// The file is also overwritten with zeros to ensure it cannot be reused by
/// another process.
#[allow(deprecated)]
pub fn load_stage1_dice_data<A: Attester + Serializable + ApplicationKeysAttester>()
-> anyhow::Result<A> {
    load_stage1_dice_data_from_path(STAGE1_DICE_DATA_PATH)
}

#[allow(deprecated)]
fn load_stage1_dice_data_from_path<A: Attester + Serializable + ApplicationKeysAttester>(
    path: &str,
) -> anyhow::Result<A> {
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
        .context("couldn't open DICE data file")?;
    let size = file.metadata().map(|m| m.len() as usize).unwrap_or(0);

    let mut buffer = Vec::with_capacity(size);
    file.read_to_end(&mut buffer).context("couldn't read DICE data from file")?;

    let result = A::deserialize(&buffer[..]).context("couldn't parse DICE data")?;

    buffer.zeroize();
    file.rewind()?;
    let zeros: Vec<u8> = vec![0; size];
    // Write `size` bytes of value zero over the file in an attempt to overwrite
    // (wipeout) the keys in the memory. Truncating the file or deleting it
    // leaves the data in the memory and might be accessible by scanning the
    // memory.
    // Still the following line does not guarantee overwriting the keys as the
    // filesystem might pick other memory pages to write the data on.
    file.write_all(&zeros).context("couldn't overwrite DICE data file")?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use oak_attestation::dice::DiceAttester;

    use super::*;

    #[test]
    fn test_load_stage1_dice_data() {
        const DICE_DATA_PATH: &str = "dice";
        const DICE_DATA_SIZE: usize = 2489;

        fs::copy(
            oak_file_utils::data_path("oak_containers/orchestrator/testdata/test_dice"),
            DICE_DATA_PATH,
        )
        .unwrap();

        load_stage1_dice_data_from_path::<DiceAttester>(DICE_DATA_PATH).unwrap();
        let mut file = OpenOptions::new().read(true).open(DICE_DATA_PATH).unwrap();
        let mut buffer = Vec::with_capacity(DICE_DATA_SIZE);
        file.read_to_end(&mut buffer).unwrap();
        assert_eq!(buffer.len(), DICE_DATA_SIZE);
        assert_eq!(buffer, vec![0; DICE_DATA_SIZE]);
    }
}
