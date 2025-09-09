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
use clap::Parser;
use digest_util::hex_digest_from_typed_hash;
use intoto::statement::make_statement;
use oak_time::{Duration, Instant};
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
    pub issued_on: Instant,

    #[arg(from_global)]
    output: flags::Output,
}

impl EndorseCommand {
    pub async fn run(&self) -> anyhow::Result<()> {
        let writer = self.output.open()?;

        let name = self.image.repository().to_string();
        let typed_hash = self.image.digest().context("missing digest in OCI reference")?;
        let digest = hex_digest_from_typed_hash(typed_hash)?;
        let claim_types = self.claims.claims.iter().map(|x| &**x).collect();
        let statement = make_statement(
            &name,
            &digest,
            self.issued_on,
            self.issued_on,
            self.issued_on + self.valid_for,
            claim_types,
        );

        serde_json::to_writer_pretty(writer, &statement)
            .context("serializing endorsement statement")?;

        Ok(())
    }
}
