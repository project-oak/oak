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

const QUOTE_CONFIGFS_PATH: &str = "/sys/kernel/config/tsm/report";
const RTMRS_CONFIGFS_PATH: &str = "/sys/kernel/config/tsm/rtmrs";
const MAX_READ_WAIT_MILLIS: u64 = 5000;
const THROTTLING_DELAY_MILLIS: u64 = 100;

use std::{
    path::{Path, PathBuf},
    time::Duration,
};

use anyhow::anyhow;
use sha2::{Digest, Sha384};
use tokio::{
    fs::{read, try_exists, write},
    sync::Mutex,
    time::timeout,
};

struct Rtmrs;

static QUOTE_LOCK: Mutex<u64> = Mutex::const_new(0);
static RTMR_LOCK: Mutex<Rtmrs> = Mutex::const_new(Rtmrs);

/// Create a hardware quote for this confidential VM.
///
/// On Intel platforms, the round trip time could be ~3 seconds.
/// The simplest way to generate a quote is
/// $ report=/sys/kernel/config/tsm/report/report0
/// $ mkdir $report
/// $ dd if=/dev/urandom bs=64 count=1 > $report/inblob
/// $ hexdump -C $report/outblob
pub async fn get_quote(data: [u8; 64]) -> anyhow::Result<Vec<u8>> {
    // QUOTE_CONFIGFS_PATH must present
    if !(try_exists(QUOTE_CONFIGFS_PATH).await?) {
        return Err(anyhow!("Directory {} doesn't exist!", QUOTE_CONFIGFS_PATH));
    }

    // We assume that every access to config tsm requires this lock
    let mut n = QUOTE_LOCK.lock().await;

    // Increment the request number
    *n += 1;

    // Create one directory for each quote request. Starting from 1.
    let dir = Path::new(QUOTE_CONFIGFS_PATH);
    let report_dir: PathBuf = dir.join(format!("report{}", n));
    tokio::fs::create_dir(report_dir.as_path()).await?;

    // Create and write the inblob file which contains the input data.
    write(report_dir.as_path().join("inblob"), data).await?;

    // Set up timeout time. If something stucks, we would not be blocked.
    let read_time = tokio::time::Duration::from_millis(MAX_READ_WAIT_MILLIS);

    // Wait up to 5 seconds. Return the quote.
    Ok(timeout(read_time, read(report_dir.join("outblob"))).await??)
}

// RTMR definitions and their indexes
#[derive(Copy, Clone)]
pub enum RTMR {
    RTMR0 = 0,
    RTMR1 = 1,
    RTMR2 = 2,
    RTMR3 = 3,
}

/// Extend RTMRs using the configfs tsm API.
/// Note:
///   1. Userspace can only extend RTMR 2 and 3.
///   2. Create only one directory for each RTMR and create a `index` file there
///   3. Place a file named "digest" with 384-bit data and read from it for
///      output
pub async fn extend(index: RTMR, data: [u8; 48]) -> anyhow::Result<Vec<u8>> {
    extend_at(Path::new(RTMRS_CONFIGFS_PATH), index, data).await
}

/// Implements [`extend`] for the RTMR configfs directory `rtmrs_path`.
async fn extend_at(rtmrs_path: &Path, index: RTMR, data: [u8; 48]) -> anyhow::Result<Vec<u8>> {
    // RTMRS_CONFIGFS_PATH must present
    if !(try_exists(rtmrs_path).await?) {
        return Err(anyhow!("Directory {} doesn't exist!", rtmrs_path.display()));
    }

    // We assume that every access to config tsm rtmr requires this lock
    let _guard = RTMR_LOCK.lock().await;

    let rtmr_dir: PathBuf = rtmrs_path.join(format!("rtmrs{}", index as usize));

    // Create a directory for each RTMR and set up the index
    if !(try_exists(rtmr_dir.as_path()).await?) {
        // Stage1 creates the dir for RTMR2 and the dir exists after configfs
        // is mounted again. So the create_dir can fail for 1 single time.
        if tokio::fs::create_dir(rtmr_dir.as_path()).await.is_ok() {
            // Write to the index file if the directory is created successfully.
            write(rtmr_dir.as_path().join("index"), (index as usize).to_string().as_bytes())
                .await?;
        }
    }

    // The corresponding directory exists and index file is ready
    // Next, write to the digest file. Must be a 384-bit data for TDX.
    //
    // configfs only buffers writes to the `digest` binary attribute. The RTMR is
    // extended when the file is closed and the result of that is discarded, so
    // a failed extend (e.g. a busy TDCALL) is not reported by the write. Read the
    // RTMR back and compare it with the expected value instead.
    let digest_path = rtmr_dir.join("digest");
    let initial = read_digest(&digest_path).await?;
    let expected = Sha384::new().chain_update(&initial).chain_update(data).finalize().to_vec();
    for _ in 0..3 {
        write(&digest_path, data).await?;
        let digest = read_digest(&digest_path).await?;
        if digest == expected {
            return Ok(digest);
        }
        if digest != initial {
            return Err(anyhow!("RTMR{} has an unexpected value after extend", index as usize));
        }
        // The RTMR was not extended, retry.
        tokio::time::sleep(Duration::from_millis(THROTTLING_DELAY_MILLIS)).await;
    }
    Err(anyhow!("failed to extend RTMR{}", index as usize))
}

/// Reads the current value of an RTMR from its `digest` file.
async fn read_digest(digest_path: &Path) -> anyhow::Result<Vec<u8>> {
    // Set up timeout time.
    let read_time = tokio::time::Duration::from_millis(MAX_READ_WAIT_MILLIS);

    // Wait up to 5 seconds.
    Ok(timeout(read_time, read(digest_path)).await??)
}

#[cfg(test)]
mod tests {
    use std::{fs, os::unix::fs::symlink};

    use googletest::prelude::*;

    use super::*;

    const DATA: [u8; 48] = [0x42; 48];

    #[googletest::gtest]
    #[tokio::test]
    async fn extend_fails_if_rtmr_is_unchanged() -> anyhow::Result<()> {
        let rtmrs = tempfile::tempdir()?;
        let rtmr_dir = rtmrs.path().join("rtmrs2");
        fs::create_dir(&rtmr_dir)?;
        // Accepts the write but keeps its value, like an RTMR whose extend failed
        // when configfs released the file.
        symlink("/dev/null", rtmr_dir.join("digest"))?;

        expect_that!(extend_at(rtmrs.path(), RTMR::RTMR2, DATA).await, err(anything()));
        Ok(())
    }

    #[googletest::gtest]
    #[tokio::test]
    async fn extend_fails_if_rtmr_has_unexpected_value() -> anyhow::Result<()> {
        let rtmrs = tempfile::tempdir()?;
        let rtmr_dir = rtmrs.path().join("rtmrs2");
        fs::create_dir(&rtmr_dir)?;
        // Reads back the written data instead of SHA-384(previous || data).
        fs::write(rtmr_dir.join("digest"), [0u8; 48])?;

        expect_that!(extend_at(rtmrs.path(), RTMR::RTMR2, DATA).await, err(anything()));
        Ok(())
    }
}
