//
// Copyright 2025 The Project Oak Authors
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

use sha2::{Digest, Sha384};

const MEM_PAGE_ADD_HEADER: &[u8] = b"MEM.PAGE.ADD";
const MR_EXTEND_HEADER: &[u8] = b"MR.EXTEND";
const PAGE_SIZE: u64 = 0x1000;
const CHUNK_SIZE: usize = 256;
const EXTENSION_BUFFER_SIZE: usize = 128;

// Intel TDX Application Binary Interface (ABI) Reference Draft 1.5.05.44
// 5.3.20. TDH.MEM.PAGE.ADD Leaf
//
// Extension is done using SHA384 with a 128B extension buffer composed
// as follows:
// * Bytes 0 through 11 contain the ASCII string “MEM.PAGE.ADD”.
// * Bytes 16 through 23 contain the GPA (in little-endian format).
// * All the other bytes contain 0.
fn add_page(addr: u64) -> [u8; EXTENSION_BUFFER_SIZE] {
    let mut buf = [0; EXTENSION_BUFFER_SIZE];
    buf[..MEM_PAGE_ADD_HEADER.len()].copy_from_slice(MEM_PAGE_ADD_HEADER);
    buf[16..24].copy_from_slice(&addr.to_le_bytes());
    buf
}

// Intel TDX Application Binary Interface (ABI) Reference Draft 1.5.05.44
// 5.3.44. TDH.MR.EXTEND Leaf
//
// Extend TDCS.MRTD with the chunk’s GPA and contents. Extension is done
// using SHA384, with three 128B extension buffers. The first extension
// buffer is composed as follows:
// * Bytes 0 through 8 contain the ASCII string “MR.EXTEND”.
// * Bytes 16 through 23 contain the GPA (in little-endian format).
// * All the other bytes contain 0.
// The other two extension buffers contain the chunk’s contents.
fn extend_256_byte(
    addr: u64,
    chunk: &[u8],
) -> ([u8; EXTENSION_BUFFER_SIZE], [u8; EXTENSION_BUFFER_SIZE], [u8; EXTENSION_BUFFER_SIZE]) {
    let mut buf1 = [0; EXTENSION_BUFFER_SIZE];
    buf1[..MR_EXTEND_HEADER.len()].copy_from_slice(MR_EXTEND_HEADER);
    buf1[16..24].copy_from_slice(&addr.to_le_bytes());

    let mut buf2 = [0; EXTENSION_BUFFER_SIZE];
    buf2.copy_from_slice(&chunk[..EXTENSION_BUFFER_SIZE]);

    let mut buf3 = [0; EXTENSION_BUFFER_SIZE];
    buf3.copy_from_slice(&chunk[EXTENSION_BUFFER_SIZE..CHUNK_SIZE]);

    (buf1, buf2, buf3)
}

/// Calculates the MR_TD measurement for a TD's initial state.
///
/// This function simulates the SHA384 measurement of the TD's initial state by
/// recording the sequence of MEM.PAGE.ADD and MR.EXTEND seamcalls. The order of
/// these calls is crucial for the measurement.
///
/// The algorithm operates on a per-section basis within the firmware. For each
/// section, it performs the following steps:
///
/// 1. **Page Addition:** Adds blank 4KB pages to the TD using MEM.PAGE.ADD,
///    corresponding to the section's size and starting address.
/// 2. **Content Measurement (MR.EXTEND):** If the section has the "MR.EXTEND"
///    attribute set, it measures the content of the section in 256-byte chunks
///    using MR.EXTEND. This is done by iterating over the section's memory and
///    making a separate MR.EXTEND call for each chunk.
///
/// In Oak, the `stage0_bin_tdx` has the following four sections:
///
/// * TD_HOB: 2 pages, starting at 0x100000
/// * Mailbox: 1 page, starting at 0x102000
/// * Binary Firmware Volume (BFV): 512 pages, starting at 0xffe00000
/// * Ram low: 160 pages, starting at 0x0
///
/// Only the BFV section has the MR.EXTEND attribute.  Therefore, the TDX module
/// performs the following sequence of actions:
///
/// ```
/// MEM.PAGE.ADD(0x100000)
/// MEM.PAGE.ADD(0x101000)
/// MEM.PAGE.ADD(0x102000)
/// MEM.PAGE.ADD(0xFFE00000 … 0xFFFF0000) // 512 pages
/// MR.EXTEND(0xFFE00000.. 0xFFFFFF00) // 256B chunk x 8192 times
/// MEM.PAGE.ADD(0x0..0x9F000) // 160 pages
/// ```
///
/// The function effectively reproduces this sequence to calculate the MR_TD
/// measurement.
pub fn mr_td_measurement(stage0_bin: &[u8]) -> Vec<u8> {
    assert_eq!(stage0_bin.len(), 2 * 1024 * 1024);

    let mut hasher = Sha384::new();

    hasher.update(add_page(0x10_0000));
    hasher.update(add_page(0x10_1000));
    hasher.update(add_page(0x10_2000));

    for i in 0..512 {
        hasher.update(add_page(0xffe0_0000 + 0x1000 * i));
    }

    for i in 0..8192 {
        let chunk_offset = i * CHUNK_SIZE;
        let chunk = &stage0_bin[chunk_offset..chunk_offset + CHUNK_SIZE];
        let (buf1, buf2, buf3) = extend_256_byte(0xffe0_0000 + chunk_offset as u64, chunk);
        hasher.update(buf1);
        hasher.update(buf2);
        hasher.update(buf3);
    }

    for i in 0..160 {
        hasher.update(add_page(PAGE_SIZE * i));
    }

    let result = hasher.finalize();

    result.as_slice().into()
}

#[cfg(test)]
mod tests {
    use hex::ToHex;
    use oak_file_utils::data_path;

    use super::*;

    #[test]
    fn test_mr_td_is_measured_correctly() {
        const STAGE0_BIN_PATH: &str =
            "external/stage0_tdx_bin_for_test/file/stage0_tdx_bin_for_test";
        let stage0_bin = std::fs::read(data_path(STAGE0_BIN_PATH)).unwrap();
        let mr_td = mr_td_measurement(&stage0_bin);
        assert_eq!(mr_td.len(), 48);
        let expected_hash_str = "7e63acc88a8870e33957754f12913d7a533178e171c26e58b91f6674ecb5e091b76d0cd742e703f97d7c54451e64fd00";
        let actual_hash_str = mr_td.encode_hex::<String>().to_string();
        assert_eq!(actual_hash_str, expected_hash_str);
    }
}
