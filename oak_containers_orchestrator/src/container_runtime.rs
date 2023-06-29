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

/// Representation of a minimal OCI filesystem bundle config, including just the required fields
/// Ref: https://github.com/opencontainers/runtime-spec/blob/467fd17d4f2a987fa00051ce44b69bf9620e2ee6/config.md
#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfig {
    process: OciFilesystemBundleConfigProcess,
    root: OciFilesystemBundleConfigRoot,
}

#[derive(serde::Deserialize)]
struct OciFilesystemBundleConfigProcess {
    user: OciFilesystemBundleConfigProcessUser,
    args: Vec<String>,
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

// Directory at which the container OCI filesystem bundle will be unpacked
const CONTAINER_DIR: &str = "/oak_container";

pub async fn run(container_bundle: &[u8]) -> Result<(), anyhow::Error> {
    tokio::fs::create_dir(CONTAINER_DIR).await?;
    tar::Archive::new(&container_bundle[..]).unpack(CONTAINER_DIR)?;

    let oci_filesystem_bundle_config: OciFilesystemBundleConfig = {
        let file_path = {
            let mut base = std::path::PathBuf::from(CONTAINER_DIR);
            base.push("config.json");
            base
        };
        let oci_filesystem_bundle_config_file = tokio::fs::read_to_string(file_path).await?;

        serde_json::from_str(&oci_filesystem_bundle_config_file)?
    };

    // mount host devices inside the container directory to allow the
    // trusted application to communicate with the outside
    {
        run_command_and_log_output(
            tokio::process::Command::new("rm")
                .current_dir(CONTAINER_DIR)
                .arg("-rf")
                .arg("dev"),
        )
        .await?;
        run_command_and_log_output(
            tokio::process::Command::new("mkdir")
                .current_dir(CONTAINER_DIR)
                .arg("dev"),
        )
        .await?;
        run_command_and_log_output(
            tokio::process::Command::new("mount")
                .current_dir(CONTAINER_DIR)
                .arg("--rbind")
                .arg("/dev")
                .arg("dev/"),
        )
        .await?;
    }

    let container_rootfs_path = {
        let mut base = std::path::PathBuf::from(CONTAINER_DIR);
        base.push(oci_filesystem_bundle_config.root.path);
        base
    };

    // start the trusted application in a chroot jail of the container
    run_command_and_log_output(
        tokio::process::Command::new("chroot")
            .arg(format!(
                "--userspec={}:{}",
                oci_filesystem_bundle_config.process.user.uid,
                oci_filesystem_bundle_config.process.user.gid,
            ))
            .arg(container_rootfs_path)
            .args(oci_filesystem_bundle_config.process.args),
    )
    .await?;

    Ok(())
}
