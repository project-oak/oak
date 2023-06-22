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

#![feature(never_type)]

mod client;
mod image;

use anyhow::Context;
use clap::Parser;
use client::LauncherClient;
use nix::mount::{mount, MsFlags};
use std::{error::Error, fs::create_dir, path::Path};

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value_t = 2)]
    launcher_vsock_cid: u32,

    #[arg(long, default_value_t = 8080)]
    launcher_vsock_port: u32,

    #[arg(default_value = "/sbin/init")]
    init: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    // Overmount an empty ramfs to be used as the new root.
    mount(
        None::<&str>,
        "/",
        Some("ramfs"),
        MsFlags::empty(),
        None::<&str>,
    )
    .context("overmounting root")?;

    // musl expects /proc to be mounted, otherwise libc calls such as realpath(2) will fail.
    create_dir("/proc")?;
    mount(
        None::<&str>,
        "/proc",
        Some("proc"),
        MsFlags::MS_NOEXEC | MsFlags::MS_NOSUID | MsFlags::MS_NODEV,
        None::<&str>,
    )?;

    let mut client = LauncherClient::new(args.launcher_vsock_cid, args.launcher_vsock_port)
        .await
        .context("creating the launcher client")?;

    image::load(&mut client, Path::new("/")).await?;
    image::switch(&args.init).context("switching to the system image")?
}
