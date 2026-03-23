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

use std::{
    collections::BTreeSet,
    fs, io,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use clap::Parser;
use flate2::read::GzDecoder;
use oak_digest::{Digest, Sha256, Sha384, Sha512};
use serde::Deserialize;

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(name = "crate_vendor", about = "cargo vendor replacement")]
struct Args {
    #[arg(long, default_value = "Cargo.lock")]
    lockfile: PathBuf,

    #[arg(long, default_value = "vendor")]
    output_dir: PathBuf,

    #[arg(long)]
    config_dir: Option<PathBuf>,

    #[arg(long)]
    dry_run: bool,
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
    env_logger::init();
    let args = Args::parse();

    if let Err(e) = run(&args) {
        eprintln!("crate_vendor error: {e:#}");
        std::process::exit(1);
    }
}

fn run(args: &Args) -> Result<()> {
    let lockfile_content = fs::read_to_string(&args.lockfile)
        .with_context(|| format!("reading lockfile {:?}", args.lockfile))?;
    let packages = parse_lockfile(&lockfile_content).context("parsing Cargo.lock")?;

    let registry_packages: Vec<&Package> = packages.iter().filter(|p| p.is_crates_io()).collect();

    if registry_packages.is_empty() {
        log::info!("no registry packages found in lockfile");
        return Ok(());
    }

    log::info!("found {} registry packages in {:?}", registry_packages.len(), args.lockfile,);

    if args.dry_run {
        for pkg in &registry_packages {
            println!("{}: {}", pkg.vendor_dir_name(), pkg.download_url());
        }
        println!("\n{} crates would be downloaded (dry run)", registry_packages.len());
        return Ok(());
    }

    fs::create_dir_all(&args.output_dir)
        .with_context(|| format!("creating output directory {:?}", args.output_dir))?;

    let mut downloaded = 0u32;
    let mut skipped = 0u32;
    let mut crate_names = BTreeSet::new();

    for pkg in &registry_packages {
        let dest_dir = args.output_dir.join(pkg.vendor_dir_name());
        let checksum_file = dest_dir.join(".cargo-checksum.json");
        crate_names.insert(pkg.vendor_dir_name());

        if checksum_file.exists() {
            log::debug!("skipping {} (already vendored)", pkg.vendor_dir_name());
            skipped += 1;
            continue;
        }

        log::info!("downloading {}", pkg.vendor_dir_name());

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

        fs::write(&checksum_file, checksum_json.to_string())
            .with_context(|| format!("writing {:?}", checksum_file))?;

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
        log::debug!("attempting to fetch from {}", url);
        match waki::Client::new()
            .get(url)
            .connect_timeout(std::time::Duration::from_secs(30))
            .send()
        {
            Ok(response) => match response.body() {
                Ok(bytes) => {
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
                    last_err = anyhow::anyhow!("failed to read response body from {url}: {e}");
                }
            },
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
/// This function decompresses the provided bytes, reads the TAR archive, and
/// extracts all files into `dest_dir`. It automatically strips the first path
/// component from each entry (which in `.crate` files is typically the
/// `name-version` root directory) so that the contents are placed directly at
/// the root of `dest_dir`.
///
/// If `dest_dir` already exists, it is completely removed and recreated before
/// extraction.
fn extract_crate(crate_bytes: &[u8], dest_dir: &Path) -> Result<()> {
    let gz = GzDecoder::new(io::Cursor::new(crate_bytes));
    let mut archive = tar::Archive::new(gz);

    if dest_dir.exists() {
        fs::remove_dir_all(dest_dir)
            .with_context(|| format!("removing existing directory {:?}", dest_dir))?;
    }
    fs::create_dir_all(dest_dir).with_context(|| format!("creating directory {:?}", dest_dir))?;

    for entry in archive.entries().context("reading tar entries")? {
        let mut entry = entry.context("reading tar entry")?;
        let path = entry.path().context("reading entry path")?.into_owned();

        let stripped = path.components().skip(1).collect::<PathBuf>();

        if stripped.as_os_str().is_empty() {
            continue;
        }

        let dest = dest_dir.join(&stripped);

        if entry.header().entry_type().is_dir() {
            fs::create_dir_all(&dest).with_context(|| format!("creating directory {:?}", dest))?;
        } else {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent)
                    .with_context(|| format!("creating parent directory {:?}", parent))?;
            }
            let mut file =
                fs::File::create(&dest).with_context(|| format!("creating file {:?}", dest))?;
            io::copy(&mut entry, &mut file).with_context(|| format!("writing file {:?}", dest))?;
        }
    }

    Ok(())
}

fn write_cargo_config(config_dir: &Path, vendor_dir: &Path) -> Result<()> {
    fs::create_dir_all(config_dir)
        .with_context(|| format!("creating config directory {:?}", config_dir))?;

    let config_path = config_dir.join("config.toml");
    let vendor_path = vendor_dir.display();

    let config = format!(
        r#"# Auto-generated by crate_vendor. Do not edit.
#
# Use `cargo build --frozen` to build using only vendored sources.

[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "{vendor_path}"
"#
    );

    fs::write(&config_path, config).with_context(|| format!("writing {:?}", config_path))?;

    log::info!("wrote {:?}", config_path);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fetch_with_valid_digest() {
        // Known checksum for anyhow 1.0.98
        let expected_hex = "e16d2d3311acee920a9eb8d33b8cbc1787ce4a264e85f964c2404b969bdcd487";
        let expected_digest = Digest::from_typed_hash(&format!("sha2-256:{}", expected_hex))
            .expect("valid typed hash");

        let urls = vec!["https://static.crates.io/crates/anyhow/anyhow-1.0.98.crate".to_string()];

        let result = fetch_file_with_digest(&expected_digest, &urls);
        assert!(result.is_ok(), "fetching a valid crate should succeed");
    }

    #[test]
    fn test_fetch_with_invalid_digest() {
        let expected_hex = "0000000000000000000000000000000000000000000000000000000000000000";
        let expected_digest = Digest::from_typed_hash(&format!("sha2-256:{}", expected_hex))
            .expect("valid typed hash");

        let urls = vec!["https://static.crates.io/crates/anyhow/anyhow-1.0.98.crate".to_string()];

        let result = fetch_file_with_digest(&expected_digest, &urls);
        assert!(result.is_err(), "fetching with wrong checksum should fail");

        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("failed to fetch file with digest"),
            "error message should cite the digest mismatch"
        );
    }
}
