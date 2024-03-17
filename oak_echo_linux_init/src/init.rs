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

use std::{env::set_current_dir, fs::create_dir};

use nix::mount::{mount, MsFlags};

/// Performs the minimum initialization required from the initial process on
/// Linux to allow an application on an initial RAM disk to operate as expected.
pub fn init() -> anyhow::Result<()> {
    set_current_dir("/")?;

    // Create mount points.
    create_dir("/proc")?;
    create_dir("/sys")?;

    // Mount pseudo file systems.
    mount::<str, str, str, str>(
        Some("proc"),
        "proc",
        Some("proc"),
        MsFlags::MS_NODEV | MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC,
        None,
    )?;
    mount::<str, str, str, str>(
        Some("dev"),
        "dev",
        Some("devtmpfs"),
        MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC,
        None,
    )?;
    mount::<str, str, str, str>(
        Some("sysfs"),
        "sys",
        Some("sysfs"),
        MsFlags::MS_NODEV | MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC,
        None,
    )?;

    Ok(())
}
