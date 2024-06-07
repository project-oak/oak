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

#![feature(iterator_try_collect)]
#![feature(never_type)]

mod client;
mod dice;
mod image;

use std::{
    error::Error,
    fs::{self, create_dir},
    io::ErrorKind,
    path::Path,
    str::FromStr,
    time::Instant,
};

use anyhow::Context;
use clap::Parser;
use client::LauncherClient;
use futures_util::TryStreamExt;
use nix::{
    mount::{mount, umount, MsFlags},
    unistd::{chdir, chroot},
};
use oak_proto_rust::oak::attestation::v1::DiceData;
use prost::Message;
use tokio::process::Command;
use tonic::transport::Uri;
use x86_64::PhysAddr;

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value = "http://10.0.2.100:8080")]
    launcher_addr: Uri,

    #[arg(long, default_value = "/sbin/init")]
    init: String,

    #[arg(long = "oak-dice", value_parser = try_parse_phys_addr)]
    dice_addr: PhysAddr,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    if !Path::new("/dev").try_exists()? {
        create_dir("/dev").context("error creating /dev")?;
    }
    mount(None::<&str>, "/dev", Some("devtmpfs"), MsFlags::empty(), None::<&str>)
        .context("error mounting /dev")?;

    Command::new("/mke2fs").args(["/dev/ram0"]).spawn()?.wait().await?;
    if !Path::new("/rootfs").try_exists()? {
        create_dir("/rootfs").context("error creating /rootfs")?;
    }
    mount(Some("/dev/ram0"), "/rootfs", Some("ext4"), MsFlags::empty(), None::<&str>)
        .context("error mounting ramdrive to /rootfs")?;

    // Mount /sys so that we can read the memory map.
    if !Path::new("/sys").try_exists()? {
        create_dir("/sys").context("error creating /sys")?;
    }
    mount(None::<&str>, "/sys", Some("sysfs"), MsFlags::empty(), None::<&str>)
        .context("error mounting /sys")?;

    let mut dice_builder = dice::extract_stage0_dice_data(args.dice_addr)?;

    // Unmount /sys and /dev as they are no longer needed.
    umount("/sys").context("failed to unmount /sys")?;
    umount("/dev").context("failed to unmount /dev")?;

    // switch_root(8) magic
    chdir("/rootfs").context("failed to chdir to /rootfs")?;
    mount(Some("/rootfs"), "/", None::<&str>, MsFlags::MS_MOVE, None::<&str>)
        .context("failed to move /rootfs to /")?;
    chroot(".").context("failed to chroot to .")?;
    chdir("/").context("failed to chdir to /")?;

    let mut client = LauncherClient::new(args.launcher_addr)
        .await
        .context("error creating the launcher client")?;

    let buf = {
        let now = Instant::now();
        let buf = client.get_oak_system_image().await.context("error fetching system image")?;
        eprintln!("stage1: system image loaded in {} s", now.elapsed().as_secs_f64());
        buf
    };

    let system_image_claims = dice::measure_system_image(&buf);

    // For safety we generate the DICE data for the next layer before processing the
    // compressed system image. This consumes the `DiceBuilder` which also
    // clears the ECA private key provided by Stage 0.
    dice_builder.add_layer(system_image_claims)?;
    let dice_data: DiceData = dice_builder.serialize();

    image::extract(&buf, Path::new("/")).await.context("error loading the system image")?;

    // If the image didn't contain a `/etc/machine-id` file, create a placeholder
    // one that systemd will replace during startup. If you don't have that file
    // at all, `systemd-machine-id-setup` unit will fail.
    if !Path::new("/etc/machine-id").exists() {
        fs::write("/etc/machine-id", []).context("error writing placeholder /etc/machine-id")?;
    }

    // Write the DICE data to a well-known location as a length-delimited protobuf
    // file.
    create_dir("/oak").context("error creating `oak` directory")?;
    fs::write("/oak/dice", dice_data.encode_length_delimited_to_vec())
        .context("error writing DICE data")?;

    // Configure eth0 down, as systemd will want to manage it itself and gets
    // confused if it already has an IP address.
    {
        let (connection, handle, _) =
            rtnetlink::new_connection().context("error opening netlink connection")?;
        tokio::spawn(connection);

        // `ip link show eth0`
        let mut links = handle.link().get().match_name("eth0".to_string()).execute();

        if let Some(link) = links.try_next().await? {
            // `ip link set dev $INDEX down`
            handle.link().set(link.header.index).down().execute().await?;
        } else {
            println!("warning: eth0 not found");
        }
    }

    // We're not running under Docker, so if the system image has a lingering
    // `/.dockerenv` in it, remove it.
    fs::remove_file("/.dockerenv")
        .or_else(|err| if err.kind() == ErrorKind::NotFound { Ok(()) } else { Err(err) })
        .context("error removing `/.dockerenv`")?;

    image::switch(&args.init).context("error switching to the system image")?
}

/// Tries to parse a string slice as an address.
///
/// Assumes that the address is a hexadecimal representation if it starts with
/// "0x", or decimal otherwise.
fn try_parse_phys_addr(arg: &str) -> anyhow::Result<PhysAddr> {
    let address = if arg.starts_with("0x") {
        u64::from_str_radix(arg.strip_prefix("0x").unwrap(), 16)
            .context("couldn't parse address as a hex number")?
    } else {
        u64::from_str(arg).context("couldn't parse address as a decimal number")?
    };
    PhysAddr::try_new(address).map_err(|err| anyhow::anyhow!("invalid physical address: {}", err.0))
}
