//
// Copyright 2021 The Project Oak Authors
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

use std::{fs::File, io::Write};

use anyhow::Context;
use clap::Parser;
use lookup_data_generator::data::{
    generate_and_serialize_random_entries, generate_and_serialize_sparse_weather_entries,
    generate_and_serialize_weather_entries,
};

#[derive(Parser, Clone, Debug)]
#[command(about = "Oak Functions Lookup Data Generator")]
pub struct Opt {
    #[arg(long)]
    out_file_path: String,
    #[command(subcommand)]
    cmd: Command,
}

#[derive(Parser, Clone, Debug)]
pub enum Command {
    #[command(about = "Generate random key value pairs")]
    Random {
        #[arg(long, default_value = "20")]
        key_size_bytes: usize,
        #[arg(long, default_value = "1000")]
        value_size_bytes: usize,
        #[arg(long, default_value = "100")]
        entries: usize,
    },
    #[command(about = "Generate entries for the weather lookup example with random values")]
    Weather {},
    #[command(
        about = "Generate sparse entries plus an index for the weather lookup example with random values"
    )]
    WeatherSparse {
        #[arg(long, default_value = "100000")]
        entries: usize,
    },
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();
    let mut rng = rand::thread_rng();
    let buf = match opt.cmd {
        Command::Random {
            key_size_bytes,
            value_size_bytes,
            entries,
        } => generate_and_serialize_random_entries(
            &mut rng,
            key_size_bytes,
            value_size_bytes,
            entries,
        )
        .context("couldn't generate random entries")?,
        Command::Weather {} => generate_and_serialize_weather_entries(&mut rng)
            .context("couldn't generate weather entries")?,
        Command::WeatherSparse { entries } => {
            generate_and_serialize_sparse_weather_entries(&mut rng, entries)
                .context("couldn't generate sparse weather entries")?
        }
    };
    let mut file = File::create(opt.out_file_path).context("couldn't create out file")?;
    file.write_all(&buf).context("couldn't write to file")?;
    Ok(())
}
