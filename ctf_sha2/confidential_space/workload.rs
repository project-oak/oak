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

use std::{fs::File, io::Write, thread, time::Duration};

use base64::{Engine, engine::general_purpose::STANDARD};
use rand::{CryptoRng, RngCore, SeedableRng, rngs::StdRng};
use serde_json::json;
use sha2::{Digest, Sha256};

// Unique audience for this binary, to prevent confused deputy attacks.
// Randomly generated with
// printf "z%020lu\n" "0x$(openssl rand -hex 8)"
const OAK_CTF_SHA2_AUDIENCE: &str = "z08381475938604996746";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Generate a secret flag.
    let flag = generate_flag(&mut StdRng::from_entropy());

    // Write out the secret flag to a file. Nobody should be able to read it!
    let mut file = File::create("flag.txt")?;
    file.write_all(STANDARD.encode(flag).as_bytes())?;

    let mut hasher = Sha256::new();
    hasher.update(flag);
    let flag_digest = hasher.finalize();

    let flag_digest_string = format!("{flag_digest:x}");

    // Unfortunately, this doesn't come out in Cloud Logging as a nice structured
    // log in "jsonPayload", because Confidential Space wraps it in a string
    // value (with the "MESSAGE" key).
    eprintln!(
        "{}",
        json!({
            "flag_digest": flag_digest_string
        })
    );

    eprintln!();

    let attestation_token = oak_attestation_gcp::attestation::request_attestation_token(
        OAK_CTF_SHA2_AUDIENCE,
        &flag_digest_string,
    )
    .expect("could not request attestation token");

    eprintln!(
        "{}",
        json!({
            "attestation_token": attestation_token
        })
    );

    // Sleep for a little while. I hope nobody pwns us during this time!
    thread::sleep(Duration::from_secs(5 * 60));

    Ok(())
}

// We must use a cryptographically secure RNG.
// See <https://rust-random.github.io/book/guide-gen.html#cryptographically-secure-pseudo-random-number-generator>.
fn generate_flag<T: CryptoRng + RngCore>(rng: &mut T) -> [u8; 64] {
    let mut flag = [0; 64];
    rng.fill_bytes(&mut flag);
    flag
}
