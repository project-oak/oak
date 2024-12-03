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
use tokio::{
    fs::{read, try_exists, write},
    sync::Mutex,
    time::timeout,
};

pub struct Rtmrs {
    visited: [bool; 4],
}

static QUOTE_LOCK: Mutex<u64> = Mutex::const_new(0);
static RTMR_LOCK: Mutex<Rtmrs> = Mutex::const_new(Rtmrs { visited: [false; 4] });

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
    // RTMRS_CONFIGFS_PATH must present
    if !(try_exists(RTMRS_CONFIGFS_PATH).await?) {
        return Err(anyhow!("Directory {} doesn't exist!", RTMRS_CONFIGFS_PATH));
    }

    // We assume that every access to config tsm rtmr requires this lock
    let mut bm = RTMR_LOCK.lock().await;

    let dir = Path::new(RTMRS_CONFIGFS_PATH);
    let rtmr_dir: PathBuf = dir.join(format!("rtmrs{}", index as usize));

    // Create a directory for each RTMR and set up the index
    if !bm.visited[index as usize] || !(try_exists(rtmr_dir.as_path()).await?) {
        tokio::fs::create_dir(rtmr_dir.as_path()).await?;
        bm.visited[index as usize] = true;
        // Write to the index file.
        write(rtmr_dir.as_path().join("index"), (index as usize).to_string().as_bytes()).await?;
    }

    // The corresponding directory exists and index file is ready
    // Next, write to the digest file. Must be a 384-bit data for TDX.
    for _ in 0..3 {
        match write(rtmr_dir.as_path().join("digest"), data).await {
            Ok(_) => break,
            Err(e) => {
                if e.raw_os_error() == Some(16) {
                    // EBUSY
                    tokio::time::sleep(Duration::from_millis(THROTTLING_DELAY_MILLIS)).await;
                } else {
                    return Err(e.into());
                }
            }
        }
    }

    // Set up timeout time.
    let read_time = tokio::time::Duration::from_millis(MAX_READ_WAIT_MILLIS);

    // Wait up to 5 seconds. Return the digest.
    Ok(timeout(read_time, read(rtmr_dir.join("digest"))).await??)
}
