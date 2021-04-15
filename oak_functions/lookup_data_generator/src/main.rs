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
use bytes::BytesMut;
use oak_functions_abi::proto::Entry;
use prost::Message;
use rand::Rng;
use std::{fs::File, io::Write};
use structopt::StructOpt;

#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Lookup Data Generator")]
pub struct Opt {
    #[structopt(long, default_value = "20")]
    key_size_bytes: usize,
    #[structopt(long, default_value = "1000")]
    value_size_bytes: usize,
    #[structopt(long, default_value = "100")]
    entries: usize,
    #[structopt(long)]
    out_file_path: String,
}

fn create_bytes<R: Rng>(rng: &mut R, size_bytes: usize) -> Vec<u8> {
    let mut buf = vec![0u8; size_bytes];
    rng.fill(buf.as_mut_slice());
    buf
}

fn create_entry<R: Rng>(rng: &mut R, key_size_bytes: usize, value_size_bytes: usize) -> Entry {
    Entry {
        key: create_bytes(rng, key_size_bytes),
        value: create_bytes(rng, value_size_bytes),
    }
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
    let mut buf = BytesMut::new();
    let mut rng = rand::thread_rng();
    for _ in 0..opt.entries {
        let entry = create_entry(&mut rng, opt.key_size_bytes, opt.value_size_bytes);
        entry
            .encode_length_delimited(&mut buf)
            .context("could not encode entry")?;
    }
    let mut file = File::create(opt.out_file_path).context("could not create out file")?;
    file.write_all(&buf).context("could not write to file")?;
    Ok(())
}
