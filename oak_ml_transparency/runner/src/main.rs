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

use clap::Parser;
use log::info;
use std::{
    fs::File,
    io::{self, Read, Write},
    path::PathBuf,
    process::Command,
};

mod claim;

const RESULT_PATH: &str = "result.json";

#[derive(Parser, Clone)]
#[command(about = "Oak Model Evaluation Runner")]
struct Cli {
    #[arg(long, help = "Path to a tarball archive of a model to be evaluated")]
    model: Option<PathBuf>,
    #[arg(long, help = "Name of the model to include in the claim")]
    model_name: Option<String>,
    #[arg(long, help = "Path to an evaluation python script")]
    eval_script: Option<PathBuf>,
    #[arg(long, help = "Path to store the output in")]
    output: Option<PathBuf>,
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let cli = Cli::parse();

    let model_path = cli.model.unwrap();
    let eval_path = cli.eval_script.unwrap();
    let model_name = cli.model_name.unwrap();
    let output_path = cli.output.unwrap();

    // Compute the digest of the model (the tarball archive)
    let model_digest = sha256sum(&model_path)?;

    // Compute the digest of the eval script
    let script_digest = sha256sum(&eval_path)?;

    // Run python evaluation script
    let output = Command::new("python3")
        .arg(&eval_path)
        .arg("--model")
        .arg(model_path)
        .arg("--output")
        .arg(RESULT_PATH)
        .output()
        .expect("failed to execute process");

    if !output.status.success() {
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        anyhow::bail!(
            "Running the evaluation failed with status {}",
            output.status,
        )
    }

    let mut file = File::open(RESULT_PATH)?;
    let mut result = String::new();
    file.read_to_string(&mut result)?;

    let claim = claim::generate_claim(
        &model_name,
        &model_digest,
        &eval_path.into_os_string().into_string().unwrap(),
        &script_digest,
        &result,
    );

    let mut file = File::create(&output_path)?;
    file.write_all(claim.as_bytes())?;
    info!("the claim is stored at {output_path:?}");

    Ok(())
}

fn sha256sum(path: &PathBuf) -> anyhow::Result<String> {
    let mut file = File::open(path)?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(claim::get_sha256_hex(&bytes))
}
