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

use std::{
    fs,
    io::{self, Write},
};

use anyhow::{anyhow, Context};
use chrono::Utc;
use intoto::statement::{set_to_hex_digest, DigestSet};
use oak_proto_rust::oak::HexDigest;
use oak_time::{Duration, Instant};
use oci_spec::distribution::Reference;
use p256::{ecdsa::VerifyingKey, pkcs8::DecodePublicKey};
use serde::Deserialize;

#[derive(Clone, Debug)]
pub enum Output {
    Stdout,
    File(String),
}

impl Output {
    pub fn open(&self) -> anyhow::Result<Box<dyn Write>> {
        let writer: Box<dyn Write> = match self {
            Output::Stdout => Box::new(io::stdout()),
            Output::File(path) => Box::new(
                fs::File::create(path)
                    .with_context(|| format!("could not create output file {path}"))?,
            ),
        };
        Ok(writer)
    }
}

impl From<&str> for Output {
    fn from(path: &str) -> Self {
        if path == "-" || path.is_empty() {
            Output::Stdout
        } else {
            Output::File(path.to_string())
        }
    }
}

#[derive(Default, Debug, Clone, Deserialize)]
pub struct Claims {
    pub claims: Vec<String>,
}

pub(crate) fn parse_claims(path: &str) -> anyhow::Result<Claims> {
    let content =
        fs::read_to_string(path).with_context(|| format!("could not read claims file {path}"))?;
    let claims: Claims =
        toml::from_str(&content).with_context(|| format!("could not parse claims file {path}"))?;

    Ok(claims)
}

pub(crate) fn parse_duration(valid_for: &str) -> anyhow::Result<Duration> {
    if let Some(hours) = valid_for.strip_suffix('h') {
        let hours = hours.parse::<i64>().context("could not parse number of hours")?;
        Ok(Duration::from_hours(hours))
    } else if let Some(days) = valid_for.strip_suffix('d') {
        let days = days.parse::<i64>().context("could not parse number of days")?;
        Ok(Duration::from_days(days))
    } else if let Some(weeks) = valid_for.strip_suffix('w') {
        let weeks = weeks.parse::<i64>().context("could not parse number of weeks")?;
        Ok(Duration::from_weeks(weeks))
    } else {
        anyhow::bail!("invalid duration format: must end with 'h', 'd', or 'w'");
    }
}

pub(crate) fn parse_current_time(value: &str) -> anyhow::Result<Instant> {
    if value.is_empty() {
        Ok(Instant::from(Utc::now()))
    } else {
        Instant::try_from(value).map_err(|msg| anyhow::anyhow!(msg))
    }
}

pub(crate) fn verifying_key_parser(key_path: &str) -> anyhow::Result<VerifyingKey, anyhow::Error> {
    let public_key_pem = fs::read_to_string(key_path)?;
    VerifyingKey::from_public_key_pem(&public_key_pem)
        .map_err(|e| anyhow::anyhow!("failed to parse public key: {e}"))
}

// TODO: b/443012225 - Deduplicate multiple copies of this function.
pub(crate) fn oci_ref_to_hex_digest(oci_ref: &Reference) -> anyhow::Result<HexDigest> {
    let digest = oci_ref.digest().ok_or_else(|| anyhow!("missing digest in oci reference"))?;
    let (alg, hash) = digest.split_once(':').context("invalid digest spec in oci reference")?;
    let digest_set = DigestSet::from([(alg.to_string(), hash.to_string())]);
    set_to_hex_digest(&digest_set)
}
