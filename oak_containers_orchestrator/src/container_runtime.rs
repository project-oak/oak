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

use std::{
    os::unix::fs::lchown,
    path::{Path, PathBuf},
};

use anyhow::Context;
use nix::unistd::{Gid, Uid};
use oci_spec::runtime::{LinuxIdMapping, LinuxIdMappingBuilder, Mount, Spec};
use tokio_util::sync::CancellationToken;

pub async fn run(
    container_bundle: &[u8],
    container_dir: &Path,
    runtime_uid: Uid,
    runtime_gid: Gid,
    ipc_socket_path: &Path,
    cancellation_token: CancellationToken,
) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir_all(container_dir).await?;
    log::info!("Unpacking container bundle");
    let mut archive = tar::Archive::new(container_bundle);
    archive.unpack(container_dir)?;

    for entry in walkdir::WalkDir::new(container_dir) {
        let entry = entry?;
        lchown(
            entry.path(),
            Some(runtime_uid.into()),
            Some(runtime_gid.into()),
        )
        .context(format!("failed to chown path {:?}", entry.path()))?;
    }

    log::info!("Setting up container");

    let spec_path = container_dir.join("config.json");
    let mut spec = Spec::load(&spec_path).context("error reading OCI spec")?;
    let mut mounts = spec.mounts().as_ref().cloned().unwrap_or_default();
    mounts.push({
        let mut mount = Mount::default();
        mount.set_source(Some(ipc_socket_path.into()));
        mount.set_destination(PathBuf::from("/oak_utils/orchestrator_ipc"));
        mount.set_typ(Some("bind".to_string()));
        mount.set_options(Some(vec!["rbind".to_string()]));
        mount
    });
    spec.set_mounts(Some(mounts));
    let mut linux = spec.linux().as_ref().cloned().unwrap_or_default();
    let uid_mappings: Option<Vec<LinuxIdMapping>> = linux.uid_mappings().as_ref().map(|x| {
        x.iter()
            .map(|entry| {
                LinuxIdMappingBuilder::default()
                    .host_id(runtime_uid)
                    .container_id(entry.container_id())
                    .size(entry.size())
                    .build()
                    .unwrap()
            })
            .collect()
    });
    linux.set_uid_mappings(uid_mappings);
    let gid_mappings: Option<Vec<LinuxIdMapping>> = linux.gid_mappings().as_ref().map(|x| {
        x.iter()
            .map(|entry| {
                LinuxIdMappingBuilder::default()
                    .host_id(runtime_gid)
                    .container_id(entry.container_id())
                    .size(entry.size())
                    .build()
                    .unwrap()
            })
            .collect()
    });
    linux.set_gid_mappings(gid_mappings);
    spec.set_linux(Some(linux));
    spec.save(spec_path).context("error writing OCI spec")?;

    let mut start_trusted_app_cmd = {
        let mut cmd = tokio::process::Command::new("/bin/systemd-run");
        let container_dir: &str = container_dir
            .as_os_str()
            .try_into()
            .expect("invalid container path");
        cmd.args([
            "--property=RuntimeDirectory=oakc",
            "--property=ProtectSystem=strict",
            format!("--property=ReadWritePaths={}", container_dir).as_str(),
            format!("--uid={}", runtime_uid).as_str(),
            format!("--gid={}", runtime_gid).as_str(),
            "--pty",
            "--wait",
            "--collect",
            "/bin/runc",
            "--root=${RUNTIME_DIRECTORY}/runc",
            "run",
            format!("--bundle={}", container_dir).as_str(),
            "oakc",
        ]);
        cmd
    };

    let status = start_trusted_app_cmd.status().await.context(format!(
        "failed to run trusted app, cmd: {start_trusted_app_cmd:?}"
    ))?;
    log::info!("Container exited with status {status:?}");

    cancellation_token.cancel();
    Ok(())
}
