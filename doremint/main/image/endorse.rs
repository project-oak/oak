// Copyright 2025 The Project Oak Authors
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

use clap::Parser;

#[derive(Parser, Debug)]
#[command(about = "Endorse a container image")]
pub struct EndorseArgs {
    #[arg(long)]
    pub image_ref: String,
    #[arg(long)]
    pub image_digest: String,
    #[arg(long)]
    pub valid_for: String,
    #[arg(long)]
    pub claims_file: String,
}

impl EndorseArgs {
    pub fn run(&self) {
        println!("Endorsing image with args: {:?}", self);
    }
}
