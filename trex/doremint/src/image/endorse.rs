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

use anyhow::Context;
use chrono::{DateTime, Duration, FixedOffset};
use clap::Parser;
use endorsement::intoto::{EndorsementOptions, EndorsementStatement, Validity};
use oci_spec::distribution::Reference;

use crate::flags::{self, parse_current_time, parse_duration};

#[derive(Parser, Debug)]
#[command(about = "Endorse a container image")]
pub struct EndorseCommand {
    #[arg(from_global)]
    pub image: Reference,

    #[arg(from_global)]
    pub claims: flags::Claims,

    #[arg(long, value_parser = parse_duration, help = "A duration string indicating how long the endorsement is valid for, e.g., '30d', '12h', '1w'")]
    pub valid_for: Duration,

    #[arg(
        long,
        help = "A fixed timestamp for issuing the endorsement, in RFC3339 format",
        value_parser = parse_current_time,
        default_value = ""
    )]
    pub issued_on: DateTime<FixedOffset>,

    #[arg(from_global)]
    output: flags::Output,
}

impl EndorseCommand {
    pub async fn run(&self) -> anyhow::Result<()> {
        let writer = self.output.open()?;

        let statement = EndorsementStatement::from_container_image(
            &self.image,
            EndorsementOptions {
                issued_on: self.issued_on,
                validity: Validity {
                    not_before: self.issued_on,
                    not_after: self.issued_on + self.valid_for,
                },
                claims: self.claims.claims.clone(),
            },
        )?;

        serde_json::to_writer_pretty(writer, &statement)
            .context("could not serialize statement to JSON")?;

        Ok(())
    }
}
