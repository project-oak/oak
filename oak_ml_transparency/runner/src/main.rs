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

use std::{
    fs::File,
    io::{Read, Write},
    path::PathBuf,
};

use clap::Parser;
use log::info;

#[derive(Parser, Clone)]
#[command(about = "Oak Model Evaluation Runner")]
struct Cli {
    #[arg(long, help = "Path to a tarball archive of a model to be evaluated")]
    model: PathBuf,
    #[arg(long, help = "Name of the model to include in the claim")]
    model_name: String,
    #[arg(long, help = "Path to an evaluation python script")]
    eval_script: PathBuf,
    #[arg(long, help = "Path to store the output in")]
    output: PathBuf,
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let cli = Cli::parse();

    let model_path = cli.model;
    let eval_path = cli.eval_script;
    let model_name = cli.model_name;
    let output_path = cli.output;

    // Compute the digest of the model (the tarball archive)
    let model_digest = sha256sum(&model_path)?;

    // Compute the digest of the eval script
    let script_digest = sha256sum(&eval_path)?;

    let result =
        runner::run_evaluation(&model_path, &eval_path).expect("running the evaluation failed");

    let claim = runner::generate_claim(
        &model_name,
        &model_digest,
        &eval_path.into_os_string().into_string().unwrap(),
        &script_digest,
        &result,
    )?;

    let claim = serde_json::to_string_pretty(&claim)?;
    let mut file = File::create(&output_path)?;
    file.write_all(claim.as_bytes())?;
    info!("the claim is stored in {output_path:?}");

    Ok(())
}

fn sha256sum(path: &PathBuf) -> anyhow::Result<String> {
    let mut file = File::open(path)?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(runner::get_sha256_hex(&bytes))
}
