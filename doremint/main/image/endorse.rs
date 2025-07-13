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

use std::{fs, io::Write};

use anyhow::Context;
use chrono::{DateTime, Duration, FixedOffset};
use clap::Parser;
use doremint::statement::{DefaultStatement, DefaultStatementOptions, DigestSet, Subject};
use serde::Deserialize;

use crate::flags::{parse_current_time, parse_validity};

#[derive(Parser, Debug)]
#[command(about = "Endorse a container image")]
pub struct EndorseArgs {
    #[arg(long)]
    pub image_ref: String,
    #[arg(long)]
    pub image_digest: String,
    #[arg(long, value_parser = parse_validity, help = "A duration string indicating how long the endorsement is valid for, e.g., '30d', '12h', '1w'")]
    pub valid_for: Duration,
    #[arg(long)]
    pub claims_file: String,
    #[arg(
        long,
        help = "A fixed timestamp for issuing the endorsement, in RFC3339 format",
        value_parser = parse_current_time,
        default_value = ""
    )]
    pub issued_on: DateTime<FixedOffset>,
}

#[derive(Deserialize)]
struct Claims {
    claims: Vec<String>,
}

impl EndorseArgs {
    pub fn run(&self, writer: &mut dyn Write) -> anyhow::Result<()> {
        let claims_file_content = fs::read_to_string(&self.claims_file)
            .with_context(|| format!("could not read claims file {}", self.claims_file))?;
        let claims: Claims = toml::from_str(&claims_file_content)
            .with_context(|| format!("could not parse claims file {}", self.claims_file))?;

        let name = self.image_ref.clone();
        let (alg, val) =
            self.image_digest.split_once(':').context("invalid image digest format")?;
        let subject =
            Subject { name, digest: DigestSet::from([(alg.to_string(), val.to_string())]) };

        let statement = DefaultStatement::new(
            subject,
            DefaultStatementOptions {
                issued_on: self.issued_on,
                validity: self.valid_for,
                claims: claims.claims,
            },
        );

        serde_json::to_writer(writer, &statement)
            .context("could not serialize statement to JSON")?;

        Ok(())
    }
}
