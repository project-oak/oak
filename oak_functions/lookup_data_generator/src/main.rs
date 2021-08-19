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

use anyhow::Context;
use lookup_data_generator::data::{
    generate_and_serialize_random_entries, generate_and_serialize_sparse_weather_entries,
    generate_and_serialize_weather_entries,
};
use std::{fs::File, io::Write};
use structopt::StructOpt;

#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Lookup Data Generator")]
pub struct Opt {
    #[structopt(long)]
    out_file_path: String,
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt, Clone, Debug)]
pub enum Command {
    #[structopt(about = "Generate random key value pairs")]
    Random {
        #[structopt(long, default_value = "20")]
        key_size_bytes: usize,
        #[structopt(long, default_value = "1000")]
        value_size_bytes: usize,
        #[structopt(long, default_value = "100")]
        entries: usize,
    },
    #[structopt(about = "Generate entries for the weather lookup example with random values")]
    Weather {},
    #[structopt(
        about = "Generate sparse entries plus an index for the weather lookup example with random values"
    )]
    WeatherSparse {
        #[structopt(long, default_value = "100000")]
        entries: usize,
    },
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
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
        .context("could not generate random entries")?,
        Command::Weather {} => generate_and_serialize_weather_entries(&mut rng)
            .context("could not generate weather entries")?,
        Command::WeatherSparse { entries } => {
            generate_and_serialize_sparse_weather_entries(&mut rng, entries)
                .context("could not generate sparse weather entries")?
        }
    };
    let mut file = File::create(opt.out_file_path).context("could not create out file")?;
    file.write_all(&buf).context("could not write to file")?;
    Ok(())
}
