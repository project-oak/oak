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
use tokio::sync::oneshot::Sender;

// Directory at which the container OCI filesystem bundle will be unpacked.
const CONTAINER_DIR: &str = "/oak_container";

pub async fn run(
    container_bundle: &[u8],
    exit_notification_sender: Sender<()>,
) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir(CONTAINER_DIR).await?;
    log::info!("Unpacking container bundle");
    tar::Archive::new(container_bundle).unpack(CONTAINER_DIR)?;

    log::info!("Setting up container");

    let mut start_trusted_app_cmd = {
        let mut cmd = tokio::process::Command::new("/bin/systemd-run");
        cmd.args([
            "--service-type=forking",
            "--property=PIDFile=/run/oakc.pid",
            "--wait",
            "--collect",
            "/bin/runc",
            "--systemd-cgroup",
            "run",
            "--detach",
            "--pid-file",
            "/run/oakc.pid",
            "--bundle",
            "/oak_container",
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
