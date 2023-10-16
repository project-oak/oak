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

use std::path::{Path, PathBuf};

use anyhow::Context;
use oci_spec::runtime::{Mount, Spec};
use tokio::sync::oneshot::Sender;

pub async fn run(
    container_bundle: &[u8],
    container_dir: &Path,
    ipc_socket_path: &Path,
    exit_notification_sender: Sender<()>,
) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir_all(container_dir).await?;
    log::info!("Unpacking container bundle");
    tar::Archive::new(container_bundle).unpack(container_dir)?;

    log::info!("Setting up container");

    let spec_path = container_dir.join("config.json");
    let mut spec = Spec::load(spec_path.clone()).context("error reading OCI spec")?;
    let mut mounts = spec.mounts().as_ref().map_or(Vec::new(), |v| v.clone());
    mounts.push({
        let mut mount = Mount::default();
        mount.set_source(Some(ipc_socket_path.into()));
        mount.set_destination(PathBuf::from("/oak_utils/orchestrator_ipc"));
        mount.set_typ(Some("bind".to_string()));
        mount.set_options(Some(vec!["rbind".to_string()]));
        mount
    });
    spec.set_mounts(Some(mounts));
    spec.save(spec_path).context("error writing OCI spec")?;

    let mut start_trusted_app_cmd = {
        let mut cmd = tokio::process::Command::new("/bin/systemd-run");
        let container_dir: &str = container_dir
            .as_os_str()
            .try_into()
            .expect("invalid container path");
        cmd.args([
            "--service-type=forking",
            "--property=RuntimeDirectory=oakc",
            // PIDFile is relative to `/run`, but unfortunately can't reference `RuntimeDirectory`.
            "--property=PIDFile=oakc/oakc.pid",
            "--property=ProtectSystem=strict",
            format!("--property=ReadWritePaths={}", container_dir).as_str(),
            "--wait",
            "--collect",
            "/bin/runc",
            "--systemd-cgroup",
            "--root=${RUNTIME_DIRECTORY}/runc",
            "run",
            "--detach",
            "--pid-file=${PIDFILE}",
            format!("--bundle={}", container_dir).as_str(),
            "oakc",
        ]);
        cmd
    };

    let status = start_trusted_app_cmd.status().await.context(format!(
        "failed to run trusted app, cmd: {start_trusted_app_cmd:?}"
    ))?;
    log::info!("Container exited with status {status:?}");

    let _ = exit_notification_sender.send(());
    Ok(())
}
