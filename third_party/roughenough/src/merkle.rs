// Copyright 2017-2019 int08h LLC
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

//!
//! Merkle Tree implementation using SHA-512 and the Roughtime leaf and node tweak values.
//!

use super::{TREE_LEAF_TWEAK, TREE_NODE_TWEAK};
use ring::digest;

type Data = Vec<u8>;
type Hash = Data;

pub fn root_from_paths(mut index: usize, data: &[u8], paths: &[u8]) -> Hash {
    let mut hash = {
        let mut ctx = digest::Context::new(&digest::SHA512);
        ctx.update(TREE_LEAF_TWEAK);
        ctx.update(data);
        Hash::from(ctx.finish().as_ref())
    };

    assert_eq!(paths.len() % 64, 0);

    for path in paths.chunks(64) {
        let mut ctx = digest::Context::new(&digest::SHA512);
        ctx.update(TREE_NODE_TWEAK);

        if index & 1 == 0 {
            // Left
            ctx.update(&hash);
            ctx.update(path);
        } else {
            // Right
            ctx.update(path);
            ctx.update(&hash);
        }

        hash = Hash::from(ctx.finish().as_ref());
        index >>= 1;
    }

    hash
}
