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
use futures_util::TryStreamExt;
use nix::{
    mount::{mount, umount, MsFlags},
    unistd::{chdir, chroot},
};
use std::{
    error::Error,
    fs::{self, create_dir},
    io::ErrorKind,
    path::Path,
};
use tokio::process::Command;

#[derive(Parser, Debug)]
struct Args {
    #[arg(default_value = "http://10.0.2.100:8080")]
    launcher_addr: String,

    #[arg(default_value = "/sbin/init")]
    init: String,
}
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    if !Path::new("/dev").try_exists()? {
        create_dir("/dev").context("error creating /dev")?;
    }
    mount(
        None::<&str>,
        "/dev",
        Some("devtmpfs"),
        MsFlags::empty(),
        None::<&str>,
    )
    .context("error mounting /dev")?;

    Command::new("/mke2fs")
        .args(["/dev/ram0"])
        .spawn()?
        .wait()
        .await?;
    if !Path::new("/rootfs").try_exists()? {
        create_dir("/rootfs").context("error creating /rootfs")?;
    }
    mount(
        Some("/dev/ram0"),
        "/rootfs",
        Some("ext4"),
        MsFlags::empty(),
        None::<&str>,
    )
    .context("error mounting ramdrive to /rootfs")?;

    // switch_root(8) magic
    umount("/dev").context("failed to unmount /dev")?;
    chdir("/rootfs").context("failed to chdir to /rootfs")?;
    mount(
        Some("/rootfs"),
        "/",
        None::<&str>,
        MsFlags::MS_MOVE,
        None::<&str>,
    )
    .context("failed to move /rootfs to /")?;
    chroot(".").context("failed to chroot to .")?;
    chdir("/").context("failed to chdir to /")?;

    let mut client = LauncherClient::new(args.launcher_addr.parse()?)
        .await
        .context("error creating the launcher client")?;

    image::load(&mut client, Path::new("/"))
        .await
        .context("error loading the system image")?;

    // If the image didn't contain a `/etc/machine-id` file, create a placeholder one that systemd
    // will replace during startup. If you don't have that file at all, `systemd-machine-id-setup`
    // unit will fail.
    if !Path::new("/etc/machine-id").exists() {
        fs::write("/etc/machine-id", []).context("error writing placeholder /etc/machine-id")?;
    }

    // Configure eth0 down, as systemd will want to manage it itself and gets confused if it already
    // has an IP address.
    {
        let (connection, handle, _) =
            rtnetlink::new_connection().context("error opening netlink connection")?;
        tokio::spawn(connection);

        // `ip link show eth0`
        let mut links = handle.link().get().match_name("eth0".to_string()).execute();

        if let Some(link) = links.try_next().await? {
            // `ip link set dev $INDEX down`
            handle
                .link()
                .set(link.header.index)
                .down()
                .execute()
                .await?;
        } else {
            println!("warning: eth0 not found");
        }
    }

    // We're not running under Docker, so if the system image has a lingering `/.dockerenv` in it,
    // remove it.
    fs::remove_file("/.dockerenv")
        .or_else(|err| {
            if err.kind() == ErrorKind::NotFound {
                Ok(())
            } else {
                Err(err)
            }
        })
        .context("error removing `/.dockerenv`")?;

    image::switch(&args.init).context("error switching to the system image")?
}
