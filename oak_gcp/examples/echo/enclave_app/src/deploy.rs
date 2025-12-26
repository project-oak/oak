//
// Copyright 2024 The Project Oak Authors
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

use std::{process::Command, time::Duration};

use anyhow::Result;
use clap::Parser;
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use tempfile::NamedTempFile;

#[derive(Parser, Debug)]
#[command(name = "deploy_rs", about = "A tool for deploying the echo enclave app.", version)]
struct Args {
    #[arg(long, required = true, help = "The OCI repository to push the image to")]
    repository: String,
    #[arg(long, help = "Path to the cosign key for endorsement")]
    cosign_key: Option<String>,
    #[arg(long, help = "The GCP instance to reload")]
    instance: Option<String>,
    #[arg(long, help = "The GCP zone for the instance")]
    zone: Option<String>,
}

fn print_header() {
    println!(
        r#"
                                         &&& &&  & &&
                                     && &\/&\|& ()|/ @, &&
                                     &\/(/&/&||/& /_/)_&/_&
                                  &() &\/&|()|/&\/ '%\" & ()
                                 &_\_&&_\ |& |&&/&__%_/_& &&
                               &&   && & &| &| /& & % ()& /&&
                                ()&_---()&\&|&&-&&--%---()~
                                       &&   |||
                                             |||
                                             |||
                                       , -=-~  .-^- _

                             Oak Echo Container Deployment Tool
        "#
    );
}

fn run(message: &str, command: &mut Command) -> Result<()> {
    // Last element is used once the spinner reaches the finished state
    const TICKS: [&str; 7] = ["▹▹▹▹▹", "▸▹▹▹▹", "▹▸▹▹▹", "▹▹▸▹▹", "▹▹▹▸▹", "▹▹▹▹▸", "▪▪▪▪▪"];

    let pb = ProgressBar::new_spinner();
    pb.enable_steady_tick(Duration::from_millis(120));
    pb.set_style(
        ProgressStyle::with_template("{spinner:.blue} {msg}").unwrap().tick_strings(&TICKS),
    );
    pb.set_message(message.to_string());

    let output = command.output()?;

    if output.status.success() {
        pb.finish_with_message(format!("{} [{}]", message, "✔".green()));
        Ok(())
    } else {
        pb.finish_with_message(format!("{} [{}]", message, "✖".red()));
        Err(anyhow::anyhow!(
            "Command failed with status: {}\nstdout: {}\nstderr: {}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

fn main() -> Result<()> {
    let args = Args::parse();

    print_header();

    if args.instance.is_some() && args.zone.is_none() {
        anyhow::bail!("--zone is required when --instance is provided.");
    }

    if let Some(cosign_key_path) = &args.cosign_key {
        // If the path does not have a scheme, like gcpkms://, assume it's a local file.
        // Local files can be password protected, so we check for that and ask for the
        // password if necessary.
        if !cosign_key_path.contains("://") {
            let key_content = std::fs::read_to_string(cosign_key_path)?;
            if key_content.contains("ENCRYPTED") && std::env::var("COSIGN_PASSWORD").is_err() {
                let password = rpassword::prompt_password("Enter password for cosign key: ")?;
                std::env::set_var("COSIGN_PASSWORD", password);
            }
        }
    }

    let image_dir = "oak_gcp/examples/echo/enclave_app/image";
    let claims_path = "oak_gcp/examples/echo/enclave_app/claims.toml";

    let index_json_path = format!("{}/index.json", image_dir);
    let index_json = std::fs::read_to_string(index_json_path)?;
    let manifest: serde_json::Value = serde_json::from_str(&index_json)?;
    let image_digest = manifest["manifests"][0]["digest"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("Failed to get image digest from image manifest"))?;

    let image_uri = format!("{}@{}", args.repository, image_digest);

    run(
        &format!("Pushing OCI image to {}...", args.repository),
        Command::new("oak_gcp/examples/echo/enclave_app/push_push.sh")
            .args(["--repository", &args.repository]),
    )?;

    println!("{} Image pushed to {}", "INFO:".green(), image_uri);

    if let Some(cosign_key_path) = &args.cosign_key {
        let endorsement_file = NamedTempFile::new()?;
        let endorsement_path = endorsement_file.path().to_str().unwrap();

        run(
            "Endorsing the image...",
            Command::new("trex/doremint/doremint").args([
                "image",
                "endorse",
                "--valid-for=30d",
                &format!("--image={image_uri}"),
                &format!("--claims-toml={claims_path}"),
                &format!("--output={endorsement_path}"),
            ]),
        )?;

        run(
            "Signing endorsement...",
            Command::new("cosign").args([
                "sign",
                "--yes",
                &format!("--key={cosign_key_path}"),
                &format!("--payload={endorsement_path}"),
                &image_uri,
            ]),
        )?;
    }

    if let (Some(instance_name), Some(zone)) = (&args.instance, &args.zone) {
        let metadata = format!("tee-image-reference={image_uri}");
        run(
            "Updating VM metadata...",
            Command::new("gcloud").args([
                "compute",
                "instances",
                "add-metadata",
                instance_name,
                &format!("--zone={zone}"),
                &format!("--metadata={metadata}"),
            ]),
        )?;
    }

    Ok(())
}
