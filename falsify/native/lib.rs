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

//! Native runner for falsification tests.
//!
//! Provides [`falsify()`] which takes a [`falsify::Claim`] implementation,
//! evaluates it with input from a file, and writes the result to a TOML output
//! file.
// TODO: b/436216021 - Replace TOML with binary protobuf for the output file
// format.

use std::{
    convert::Infallible,
    fs, panic,
    path::{Path, PathBuf},
};

use clap::Parser;
use falsify::{Claim, Evaluation};
use serde::Serialize;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct FalsifyArgs {
    #[arg(long, value_parser = path_parser)]
    input_file: PathBuf,
    #[arg(long, value_parser = path_parser)]
    output_file_toml: PathBuf,
}

fn path_parser(arg_value: &str) -> Result<PathBuf, Infallible> {
    // https://bazel.build/docs/user-manual#running-executables
    Ok(Path::new(&std::env::var("BUILD_WORKING_DIRECTORY").unwrap_or_default()).join(arg_value))
}

/// The status of a falsification run, serialized as part of the TOML output
/// produced by the [`falsify()`] binary harness.
///
/// This is a flattened version of [`Evaluation`] and [`Error`] variants for
/// ease of serialization into TOML.
#[derive(Serialize)]
pub enum Status {
    // The claim is intact (was not falsified).
    Intact,
    // The claim was falsified.
    Falsified,
    // There was an error due to some malformed input. (Inconclusive)
    InputError { error_message: String },
    // The claim returned an error during execution. (Inconclusive)
    ClaimError { error_message: String },
}

/// The top-level structure of the TOML output file produced by [`falsify()`].
#[derive(Serialize)]
pub struct FalsifyResult {
    pub status: Status,
}

fn get_input_bytes(input_file: &PathBuf) -> Result<Vec<u8>, std::io::Error> {
    fs::read(input_file)
}

/// Runs a falsification test.
///
/// This function takes a [`Claim`] instance and executes it with input
/// bytes read from a file. The contract is that `claim.evaluate()` is expected
/// to never panic, for all possible inputs. The goal of researchers is to find
/// an input that falsifies the claim, i.e. makes it panic or return
/// `Ok(Evaluation::Falsified)`.
///
/// `claim` is expected to be deterministic, i.e. for a given input it should
/// always behave identically. Common causes of non-determinism are:
/// - depending on random values
/// - depending on the current time
/// - depending on the order of completion of asynchronous operations
///
/// The input and output file paths are provided as
/// command-line arguments `--input-file` and `--output-file-toml`.
///
/// The `claim` is executed in a separate panic-catching scope.
///
/// - If `claim.evaluate()` panics or returns `Ok(Evaluation::Falsified)`, the
///   test is considered [`Status::Falsified`].
/// - If `claim.evaluate()` completes successfully with
///   `Ok(Evaluation::Intact)`, the test is [`Status::Intact`].
/// - If `claim.evaluate()` returns `Err(E)`, the test results in a
///   [`Status::ClaimError`]. This is considered an *inconclusive* result.
/// - If there is an error reading the input file, the test results in a
///   [`Status::InputError`]. This is considered an *inconclusive* result.
///
/// Note: Falsification engines must treat `ClaimError` and `InputError` as
/// inconclusive exceptions (e.g., malformed test inputs). They are NOT
/// falsifications.
///
/// The result is serialized as a [`FalsifyResult`] struct into the specified
/// TOML output file.
///
/// # Panics
///
/// This function will panic if it cannot serialize the result to TOML or if it
/// cannot write to the output file.
pub fn falsify<C>(args: FalsifyArgs, claim: &C)
where
    C: Claim + panic::RefUnwindSafe,
{
    let result = match get_input_bytes(&args.input_file) {
        Ok(input_bytes) => {
            let panic_result = panic::catch_unwind(|| claim.evaluate(&input_bytes));

            match panic_result {
                Ok(inner_result) => match inner_result {
                    Ok(Evaluation::Intact) => FalsifyResult { status: Status::Intact },
                    Ok(Evaluation::Falsified) => FalsifyResult { status: Status::Falsified },
                    Err(e) => FalsifyResult {
                        status: Status::ClaimError {
                            error_message: format!("Claim returned an error: {}", e),
                        },
                    },
                },
                Err(_) => FalsifyResult { status: Status::Falsified },
            }
        }
        Err(err) => FalsifyResult {
            status: Status::InputError {
                error_message: format!(
                    "Could not read input file: {}\nError: {}",
                    args.input_file.display(),
                    err,
                ),
            },
        },
    };

    let toml_string = toml::to_string_pretty(&result).expect("Could not serialize result to TOML");
    fs::write(args.output_file_toml, toml_string).expect("Could not write to output file");
}
