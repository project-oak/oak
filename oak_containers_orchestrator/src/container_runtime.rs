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

//! Minimal implementation of a container runtime using chroot. It accepts an
//! containers in the form of an OCI filesystem bundle. However the runtime
//! itself is not OCI spec compliant.

use anyhow::Context;
use std::path::PathBuf;

/// Representation of a minimal OCI filesystem bundle config, including just the required fields.
/// Ref: <https://github.com/opencontainers/runtime-spec/blob/c4ee7d12c742ffe806cd9350b6af3b4b19faed6f/config.md>
#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfig {
    process: OciFilesystemBundleConfigProcess,
    root: OciFilesystemBundleConfigRoot,
}

#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfigProcess {
    user: OciFilesystemBundleConfigProcessUser,
    args: Vec<String>,
    cwd: std::path::PathBuf,
}

#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfigProcessUser {
    uid: u32,
    gid: u32,
}

#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfigRoot {
    path: std::path::PathBuf,
}

async fn run_command_and_log_output(
    command: &mut tokio::process::Command,
) -> Result<(), Box<std::io::Error>> {
    let output = command.output().await;
    log::info!("{:?}: {:?}", command, output);
    Ok(())
}

// Directory at which the container OCI filesystem bundle will be unpacked.
const CONTAINER_DIR: &str = "/oak_container";

async fn rmount_dir(source: PathBuf, target: PathBuf) -> Result<(), anyhow::Error> {
    if target.exists() {
        tokio::fs::remove_dir_all(&target)
            .await
            .context("failed to removing existing directories at the target")?
    }
    tokio::fs::create_dir_all(&target)
        .await
        .context("failed to create a directory at the target")?;

    run_command_and_log_output(
        tokio::process::Command::new("mount")
            .current_dir(CONTAINER_DIR)
            .arg("--rbind")
            .arg(&source)
            .arg(&target),
    )
    .await?;

    Ok(())
}

pub async fn run(container_bundle: &[u8]) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir(CONTAINER_DIR).await?;
    tar::Archive::new(container_bundle).unpack(CONTAINER_DIR)?;

    let oci_filesystem_bundle_config: OciFilesystemBundleConfig = {
        let file_path = {
            let mut base = std::path::PathBuf::from(CONTAINER_DIR);
            base.push("config.json");
            base
        };
        let oci_filesystem_bundle_config_file = tokio::fs::read_to_string(file_path).await?;

        serde_json::from_str(&oci_filesystem_bundle_config_file)?
    };

    let container_rootfs_path = {
        let mut base = std::path::PathBuf::from(CONTAINER_DIR);
        base.push(oci_filesystem_bundle_config.root.path);
        base
    };

    // mount the utility dir (includes the ipc socket) into the container
    let container_dev_path = {
        let mut base = container_rootfs_path.clone();
        base.push(crate::UTIL_DIR);
        base
    };
    rmount_dir(
        std::path::Path::new("/").join(crate::UTIL_DIR),
        container_dev_path,
    )
    .await?;

    // mount host /dev into the container
    let container_dev_path = {
        let mut base = container_rootfs_path.clone();
        base.push("dev");
        base
    };
    rmount_dir(std::path::PathBuf::from("/dev"), container_dev_path).await?;

    // mount host /sys into the container
    let container_sys_path = {
        let mut base = container_rootfs_path.clone();
        base.push("sys");
        base
    };
    rmount_dir(std::path::PathBuf::from("/sys"), container_sys_path).await?;

    // mount host /proc into the container
    let container_proc_path = {
        let mut base = container_rootfs_path.clone();
        base.push("proc");
        base
    };
    rmount_dir(std::path::PathBuf::from("/proc"), container_proc_path).await?;

    let mut start_trusted_app_cmd = {
        let mut cmd =
            tokio::process::Command::new(oci_filesystem_bundle_config.process.args[0].clone());
        cmd.args(oci_filesystem_bundle_config.process.args.as_slice()[1..].to_vec())
            .uid(oci_filesystem_bundle_config.process.user.uid)
            .gid(oci_filesystem_bundle_config.process.user.gid);
        cmd
    };

    // Prepare the trusted application
    let prep_trusted_app_process = move || {
        // Run the trusted app in a chroot enviroment of the container.
        std::os::unix::fs::chroot(container_rootfs_path.clone())?;
        // Set the specified working directory
        std::env::set_current_dir(oci_filesystem_bundle_config.process.cwd.clone())?;
        Ok(())
    };

    // Run the command to execute the trusted application. Just prior to
    // execution, prepare the child process.
    // Safety: Closure will be run the process of a child process after a fork.
    // See https://docs.rs/tokio/latest/tokio/process/struct.Command.html#safety.
    unsafe {
        let _output =
            tokio::process::Command::pre_exec(&mut start_trusted_app_cmd, prep_trusted_app_process)
                .output()
                .await;
    }

    Ok(())
}
