// Copyright 2026 The Project Oak Authors
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

//! # crate_vendor
//!
//! A standalone replacement for `cargo vendor` that downloads all
//! registry dependencies listed in a `Cargo.lock` file and extracts them
//! into a local `vendor/` directory.
//!
//! Runs inside the cleanroom sandbox:
//! - Filesystem access via `cleanroom_sdk::{read_file, write_file, ...}`
//! - Output via standard `println!` / `eprintln!`
//! - HTTP downloads via `cleanroom_sdk::http_get`
//!
//! CLI arguments are forwarded via the cleanroom runtime and parsed
//! with `clap`.  Example invocation:
//!
//! ```text
//! cleanroom run crate_vendor -- --lockfile=Cargo.lock --output-dir=vendor
//! ```

use std::{io, path::PathBuf};

use anyhow::{Context, Result};
use clap::Parser;
use oak_digest::{Digest, Sha256, Sha384, Sha512};
use serde::Deserialize;

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(name = "crate_vendor", about = "cargo vendor replacement")]
struct Args {
    #[arg(long, default_value = "Cargo.lock")]
    lockfile: String,

    #[arg(long, default_value = "vendor")]
    output_dir: String,

    #[arg(long)]
    config_dir: Option<String>,

    #[arg(long)]
    dry_run: bool,
}

// ---------------------------------------------------------------------------
// Logging helpers (use cleanroom SDK stderr)
// ---------------------------------------------------------------------------

fn log_info(msg: &str) {
    eprintln!("[INFO] {msg}");
}

fn log_debug(msg: &str) {
    eprintln!("[DEBUG] {msg}");
}

// ---------------------------------------------------------------------------
// Cargo.lock model
// ---------------------------------------------------------------------------

#[derive(Deserialize, Debug)]
struct Lockfile {
    package: Option<Vec<Package>>,
}

#[derive(Deserialize, Debug)]
struct Package {
    name: String,
    version: String,
    source: Option<String>,
    checksum: Option<String>,
}

const CRATES_IO_REGISTRY: &str = "registry+https://github.com/rust-lang/crates.io-index";

impl Package {
    fn is_crates_io(&self) -> bool {
        self.source.as_deref() == Some(CRATES_IO_REGISTRY)
    }

    /// Returns the download URL for a `.crate` archive from crates.io.
    ///
    /// The URL pattern follows the crates.io download endpoint documented at
    /// <https://doc.rust-lang.org/cargo/reference/registry-web-api.html#download>
    fn download_url(&self) -> String {
        format!(
            "https://static.crates.io/crates/{name}/{name}-{version}.crate",
            name = self.name,
            version = self.version,
        )
    }

    fn vendor_dir_name(&self) -> String {
        format!("{}-{}", self.name, self.version)
    }
}

fn parse_lockfile(content: &str) -> Result<Vec<Package>> {
    let lockfile: Lockfile = toml::from_str(content).context("parsing TOML")?;
    Ok(lockfile.package.unwrap_or_default())
}

// ---------------------------------------------------------------------------
// Core logic
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();

    if let Err(e) = run(&args) {
        eprintln!("crate_vendor error: {e:#}");
        std::process::exit(1);
    }
}

fn run(args: &Args) -> Result<()> {
    // Read the lockfile via the cleanroom filesystem proxy.
    let lockfile_bytes = cleanroom_sdk::read_file(&args.lockfile)
        .map_err(|e| anyhow::anyhow!("reading lockfile {:?}: {e}", args.lockfile))?;
    let lockfile_content =
        String::from_utf8(lockfile_bytes).context("lockfile is not valid UTF-8")?;

    let packages = parse_lockfile(&lockfile_content).context("parsing Cargo.lock")?;
    let registry_packages: Vec<&Package> = packages.iter().filter(|p| p.is_crates_io()).collect();

    if registry_packages.is_empty() {
        log_info("no registry packages found in lockfile");
        return Ok(());
    }

    log_info(&format!(
        "found {} registry packages in {:?}",
        registry_packages.len(),
        args.lockfile,
    ));

    if args.dry_run {
        for pkg in &registry_packages {
            println!("{}: {}", pkg.vendor_dir_name(), pkg.download_url());
        }
        println!("\n{} crates would be downloaded (dry run)", registry_packages.len());
        return Ok(());
    }

    let mut downloaded = 0u32;
    let mut skipped = 0u32;

    for pkg in &registry_packages {
        let dest_dir = format!("{}/{}", args.output_dir, pkg.vendor_dir_name());
        let checksum_file = format!("{dest_dir}/.cargo-checksum.json");

        // Skip if already vendored (checksum file exists).
        if cleanroom_sdk::read_file(&checksum_file).is_ok() {
            log_debug(&format!("skipping {} (already vendored)", pkg.vendor_dir_name()));
            skipped += 1;
            continue;
        }

        log_info(&format!("downloading {}", pkg.vendor_dir_name()));

        let expected_hex = pkg.checksum.as_deref().unwrap_or_default();
        if expected_hex.is_empty() {
            anyhow::bail!("missing checksum for crate {}", pkg.vendor_dir_name());
        }
        let expected_digest = Digest::from_typed_hash(&format!("sha2-256:{}", expected_hex))
            .context("invalid checksum format in lockfile")?;

        let urls = vec![pkg.download_url()];
        let crate_bytes = fetch_file_with_digest(&expected_digest, &urls)
            .with_context(|| format!("fetching {}", pkg.vendor_dir_name()))?;

        extract_crate(&crate_bytes, &dest_dir)
            .with_context(|| format!("extracting {}", pkg.vendor_dir_name()))?;

        let checksum_val = pkg.checksum.clone().unwrap_or_default();
        let checksum_json = serde_json::json!({
            "files": {},
            "package": checksum_val
        });

        cleanroom_sdk::write_file(&checksum_file, checksum_json.to_string().as_bytes())
            .map_err(|e| anyhow::anyhow!("writing {checksum_file}: {e}"))?;

        downloaded += 1;
    }

    println!(
        "vendored {} crates ({downloaded} downloaded, {skipped} already present) into {:?}",
        downloaded + skipped,
        args.output_dir,
    );

    if let Some(config_dir) = &args.config_dir {
        write_cargo_config(config_dir, &args.output_dir).context("writing .cargo/config.toml")?;
    }

    Ok(())
}

/// Sequentially attempts to download a file from a list of fallback URLs.
///
/// Upon successfully fetching the raw bytes, it computes the cryptographic hash
/// according to the algorithm specified by `expected_digest` (e.g. SHA-256).
/// It then verifies it against the expected value. If the expected value
/// doesn't match, or if a network error occurs, it continues to the next URL.
///
/// If all URLs fail (either through network issues or checksum mismatches),
/// this returns an `Err` encapsulating the reason for the final failure.
fn fetch_file_with_digest(expected_digest: &Digest, urls: &[String]) -> Result<Vec<u8>> {
    let mut last_err = anyhow::anyhow!("no URLs provided");

    for url in urls {
        log_debug(&format!("attempting to fetch from {}", url));
        match cleanroom_sdk::http_get(url, &[]) {
            Ok(response) => {
                if response.status != 200 {
                    last_err = anyhow::anyhow!("HTTP {} for {url}", response.status);
                    continue;
                }

                let bytes = response.body;
                let actual_digest = match expected_digest {
                    Digest::Sha256(_) => Digest::Sha256(Sha256::from_contents(&bytes)),
                    Digest::Sha384(_) => Digest::Sha384(Sha384::from_contents(&bytes)),
                    Digest::Sha512(_) => Digest::Sha512(Sha512::from_contents(&bytes)),
                    _ => {
                        last_err = anyhow::anyhow!(
                            "unsupported digest type for fetch: {}",
                            expected_digest.to_typed_hash()
                        );
                        continue;
                    }
                };

                if actual_digest == *expected_digest {
                    return Ok(bytes);
                } else {
                    last_err = anyhow::anyhow!(
                        "checksum mismatch for {url}: expected {}, got {}",
                        expected_digest.to_typed_hash(),
                        actual_digest.to_typed_hash()
                    );
                }
            }
            Err(e) => {
                last_err = anyhow::anyhow!("failed to HTTP GET {url}: {e}");
            }
        }
    }

    Err(last_err)
        .context(format!("failed to fetch file with digest {}", expected_digest.to_typed_hash()))
}

/// Extracts a downloaded `.crate` archive (a gzipped tarball) into the
/// specified directory.
///
/// Reads the tar entries into memory and writes each file via the cleanroom
/// filesystem proxy. The first path component (typically `name-version/`)
/// is stripped so contents are placed directly in `dest_dir`.
fn extract_crate(crate_bytes: &[u8], dest_dir: &str) -> Result<()> {
    let gz = flate2::read::GzDecoder::new(io::Cursor::new(crate_bytes));
    let mut archive = tar::Archive::new(gz);

    for entry in archive.entries().context("reading tar entries")? {
        let mut entry = entry.context("reading tar entry")?;
        let path = entry.path().context("reading entry path")?.into_owned();

        // Strip the top-level `name-version/` prefix.
        let stripped = path.components().skip(1).collect::<PathBuf>();

        if stripped.as_os_str().is_empty() {
            continue;
        }

        // Only extract regular files — directories are created implicitly
        // by write_file when the server creates parent directories.
        if !entry.header().entry_type().is_dir() {
            let dest = format!("{dest_dir}/{}", stripped.display());
            let mut contents = Vec::new();
            io::Read::read_to_end(&mut entry, &mut contents)
                .with_context(|| format!("reading tar entry {}", stripped.display()))?;
            cleanroom_sdk::write_file(&dest, &contents)
                .map_err(|e| anyhow::anyhow!("writing {dest}: {e}"))?;
        }
    }

    Ok(())
}

fn write_cargo_config(config_dir: &str, vendor_dir: &str) -> Result<()> {
    let config_path = format!("{config_dir}/config.toml");

    let config = format!(
        r#"# Auto-generated by crate_vendor. Do not edit.
#
# Use `cargo build --frozen` to build using only vendored sources.

[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "{vendor_dir}"
"#
    );

    cleanroom_sdk::write_file(&config_path, config.as_bytes())
        .map_err(|e| anyhow::anyhow!("writing {config_path}: {e}"))?;

    log_info(&format!("wrote {config_path}"));
    Ok(())
}
