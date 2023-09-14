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

use tokio::sync::oneshot::Sender;

/// Representation of a minimal OCI filesystem bundle config, including just the required fields.
/// Ref: <https://github.com/opencontainers/runtime-spec/blob/c4ee7d12c742ffe806cd9350b6af3b4b19faed6f/config.md>
#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfig {
    process: OciFilesystemBundleConfigProcess,
    root: OciFilesystemBundleConfigRoot,
}

#[derive(serde::Deserialize)]
#[allow(unused)]
struct OciFilesystemBundleConfigProcess {
    args: Vec<String>,
    #[serde(default)]
    cwd: std::path::PathBuf,
    #[serde(default)]
    env: Vec<String>,
    user: OciFilesystemBundleConfigProcessUser,
}

#[derive(serde::Deserialize)]
#[allow(unused)]
struct OciFilesystemBundleConfigProcessUser {
    uid: u32,
    gid: u32,
}

#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfigRoot {
    path: std::path::PathBuf,
}

// Directory at which the container OCI filesystem bundle will be unpacked.
const CONTAINER_DIR: &str = "/oak_container";

pub async fn run(
    container_bundle: &[u8],
    exit_notification_sender: Sender<()>,
) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir(CONTAINER_DIR).await?;
    log::info!("Unpacking container bundle");
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

    log::info!("Setting up container");

    let container_rootfs_path = {
        let mut base = std::path::PathBuf::from(CONTAINER_DIR);
        base.push(oci_filesystem_bundle_config.root.path);
        base
    };

    log::debug!(
        "Startup command: {:?}",
        oci_filesystem_bundle_config.process.args
    );

    // systemd-nspawn claims to support OCI bundles, but unfortunately it doesn't support bundles
    // in the 1.0.2-dev format. See https://github.com/systemd/systemd/issues/22148
    let mut start_trusted_app_cmd = {
        let mut nspawn = tokio::process::Command::new("/usr/bin/systemd-nspawn");
        // See https://www.freedesktop.org/software/systemd/man/systemd-nspawn.html for the list of args.
        let mut args = vec![
            "--ephemeral".to_string(),
            format!(
                "--directory={}",
                container_rootfs_path
                    .into_os_string()
                    .into_string()
                    .unwrap()
                    .as_str()
            ),
            "--as-pid2".to_string(),
            format!("--user={}", oci_filesystem_bundle_config.process.user.uid),
            format!("--bind=/{}", crate::UTIL_DIR),
            "--console=read-only".to_string(),
            "--no-pager".to_string(),
        ];

        for env in &oci_filesystem_bundle_config.process.env {
            args.push(format!("--setenv={}", env));
        }

        nspawn.args(
            args.iter()
                .chain(oci_filesystem_bundle_config.process.args.iter()),
        );
        nspawn
    };

    log::info!("nspawn: {:?}", start_trusted_app_cmd);

    let status = start_trusted_app_cmd.status().await?;
    log::info!("Container exited with status {status:?}");

    let _ = exit_notification_sender.send(());
    Ok(())
}
