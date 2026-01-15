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

mod attester;
mod client;
mod image;

use std::{
    error::Error,
    fs::{self, create_dir},
    io::ErrorKind,
    net::IpAddr,
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
use oak_attestation_types::{attester::Attester, util::Serializable};
use prost::Message;
use tokio::process::Command;
use tonic::transport::Uri;
use x86_64::PhysAddr;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(long, value_delimiter = ',')]
    pub eth0_address: Vec<String>,

    #[arg(long, default_value = "http://10.0.2.100:8080")]
    pub launcher_addr: Uri,

    #[arg(long, default_value = "/sbin/init")]
    pub init: String,

    #[arg(long = "oak-dice", value_parser = try_parse_phys_addr)]
    pub dice_addr: PhysAddr,

    #[arg(long = "oak-dice-length")]
    pub dice_data_length: usize,

    #[arg(long = "oak-event-log", value_parser = try_parse_phys_addr)]
    pub event_log: PhysAddr,
}

pub async fn main<A: Attester + Serializable + 'static>(args: &Args) -> Result<(), Box<dyn Error>> {
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

    mount(
        None::<&str>,
        "/sys/kernel/config",
        Some("configfs"),
        MsFlags::MS_NOSUID | MsFlags::MS_NODEV | MsFlags::MS_NOEXEC,
        None::<&str>,
    )
    .context("error mounting /sys/kernel/config")?;

    let mut attester = {
        // Safety: This will be the only instance of this struct.
        unsafe {
            attester::SensitiveDataMemory::<A>::new(
                args.dice_addr,
                args.event_log,
                args.dice_data_length,
            )
        }?
        .read_into_attester()?
    };

    // Configure the network, if requested.
    let (connection, handle, _) =
        rtnetlink::new_connection().context("error opening netlink connection")?;
    tokio::spawn(connection);

    // `ip link show eth0`
    let mut links = handle.link().get().match_name("eth0".to_string()).execute();

    let link = links.try_next().await?;

    if let Some(ref link) = link {
        for address in &args.eth0_address {
            let (address, prefix_len) = address.split_once('/').context("invalid IP address")?;
            let address = IpAddr::from_str(address).context("invalid IP address")?;
            let prefix_len = u8::from_str(prefix_len).context("invalid prefix length")?;

            // `ip addr add`
            handle.address().add(link.header.index, address, prefix_len).execute().await?;
        }
        // `ip link set dev $INDEX up`
        handle.link().set(link.header.index).up().execute().await?;
    } else {
        eprintln!("warning: eth0 not found");
    }

    let mut client = LauncherClient::new(args.launcher_addr.clone())
        .await
        .context("error creating the launcher client")?;

    let buf = {
        let now = Instant::now();
        let buf = client.get_oak_system_image().await.context("error fetching system image")?;
        eprintln!("stage1: system image loaded in {} s", now.elapsed().as_secs_f64());
        buf
    };

    // For safety we generate the DICE data for the next layer before processing the
    // compressed system image.
    let system_image_event = oak_containers_attestation::create_system_layer_event(buf.clone());
    let encoded_event = system_image_event.encode_to_vec();
    // Spawn the `extend`` operation on a separate thread to support cases where we
    // have async attesters.
    let attester = tokio::runtime::Handle::current()
        .spawn_blocking(move || {
            attester.extend(&encoded_event)?;
            Ok::<A, anyhow::Error>(attester)
        })
        .await??;
    let dice_data = attester.serialize();

    // Unmount /sys and /dev as they are no longer needed.
    umount("/sys/kernel/config").context("failed to unmount /sys/kernel/configfs")?;
    umount("/sys").context("failed to unmount /sys")?;
    umount("/dev").context("failed to unmount /dev")?;

    // switch_root(8) magic
    chdir("/rootfs").context("failed to chdir to /rootfs")?;
    mount(Some("/rootfs"), "/", None::<&str>, MsFlags::MS_MOVE, None::<&str>)
        .context("failed to move /rootfs to /")?;
    chroot(".").context("failed to chroot to .")?;
    chdir("/").context("failed to chdir to /")?;

    image::extract(buf, Path::new("/")).await.context("error loading the system image")?;

    // If the image didn't contain a `/etc/machine-id` file, create a placeholder
    // one that systemd will replace during startup. If you don't have that file
    // at all, `systemd-machine-id-setup` unit will fail.
    if !Path::new("/etc/machine-id").exists() {
        fs::write("/etc/machine-id", []).context("error writing placeholder /etc/machine-id")?;
    }

    // Write the DICE data to a well-known location as a length-delimited protobuf
    // file.
    create_dir("/oak").context("error creating `oak` directory")?;
    fs::write("/oak/dice", dice_data).context("error writing DICE data")?;

    // Configure eth0 down, as systemd will want to manage it itself and gets
    // confused if it already has an IP address.
    if let Some(link) = link {
        // `ip link set dev $INDEX down`
        handle.link().set(link.header.index).down().execute().await?;
    }

    // We're not running under Docker, so if the system image has a lingering
    // `/.dockerenv` in it, remove it.
    fs::remove_file("/.dockerenv")
        .or_else(|err| if err.kind() == ErrorKind::NotFound { Ok(()) } else { Err(err) })
        .context("error removing `/.dockerenv`")?;

    image::switch(
        &args.init,
        &[std::ffi::CString::new(format!("LAUNCHER_ADDR={}", args.launcher_addr)).unwrap()],
    )
    .context("error switching to the system image")?
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
