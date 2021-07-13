// Copyright (c) The camino Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use camino::Utf8PathBuf;
use structopt::StructOpt;

/// This example shows how a `Utf8Path` can be used with `structopt` argument parsing.
///
/// Using a `Utf8Path` in argument parsing in this manner means that non-UTF-8 paths can be rejected
/// at the boundaries of your program.
///
/// To run this example, run `cargo run --example structopt`.
#[derive(StructOpt)]
#[structopt(rename_all = "kebab-case")]
struct Opt {
    /// Input file
    input: Utf8PathBuf,

    /// Output file
    output: Option<Utf8PathBuf>,
}

pub fn main() {
    // Parse the arguments.
    let opt = Opt::from_args();

    // Print the input and output files.
    println!("input file: {}", opt.input);
    match &opt.output {
        Some(output) => println!("output file: {}", output),
        None => println!("no output file"),
    }
}
