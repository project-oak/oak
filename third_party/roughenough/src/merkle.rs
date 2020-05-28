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

use ring::digest;
use super::{HASH_LENGTH, TREE_LEAF_TWEAK, TREE_NODE_TWEAK};

type Data = Vec<u8>;
type Hash = Data;

///
/// Merkle Tree implementation using SHA-512 and the Roughtime leaf and node tweak values.
///
pub struct MerkleTree {
    levels: Vec<Vec<Data>>,
}

impl Default for MerkleTree {
    fn default() -> Self {
        Self::new()
    }
}

impl MerkleTree {
    ///
    /// Create a new empty Merkle Tree
    ///
    pub fn new() -> MerkleTree {
        MerkleTree {
            levels: vec![vec![]],
        }
    }

    pub fn push_leaf(&mut self, data: &[u8]) {
        let hash = self.hash_leaf(data);
        self.levels[0].push(hash);
    }

    pub fn get_paths(&self, mut index: usize) -> Vec<u8> {
        let mut paths = Vec::with_capacity(self.levels.len() * 64);
        let mut level = 0;

        while !self.levels[level].is_empty() {
            let sibling = if index % 2 == 0 { index + 1 } else { index - 1 };

            paths.extend(self.levels[level][sibling].clone());
            level += 1;
            index /= 2;
        }
        paths
    }

    pub fn compute_root(&mut self) -> Hash {
        assert!(
            !self.levels[0].is_empty(),
            "Must have at least one leaf to hash!"
        );

        let mut level = 0;
        let mut node_count = self.levels[0].len();

        while node_count > 1 {
            level += 1;

            if self.levels.len() < level + 1 {
                self.levels.push(vec![]);
            }

            if node_count % 2 != 0 {
                self.levels[level - 1].push(vec![0; HASH_LENGTH as usize]);
                node_count += 1;
            }

            node_count /= 2;

            for i in 0..node_count {
                let hash = self.hash_nodes(
                    &self.levels[level - 1][i * 2],
                    &self.levels[level - 1][(i * 2) + 1],
                );
                self.levels[level].push(hash);
            }
        }

        assert_eq!(self.levels[level].len(), 1);
        self.levels[level].pop().unwrap()
    }

    pub fn reset(&mut self) {
        for level in &mut self.levels {
            level.clear();
        }
    }

    fn hash_leaf(&self, leaf: &[u8]) -> Data {
        self.hash(&[TREE_LEAF_TWEAK, leaf])
    }

    fn hash_nodes(&self, first: &[u8], second: &[u8]) -> Data {
        self.hash(&[TREE_NODE_TWEAK, first, second])
    }

    fn hash(&self, to_hash: &[&[u8]]) -> Data {
        let mut ctx = digest::Context::new(&digest::SHA512);
        for data in to_hash {
            ctx.update(data);
        }
        Data::from(ctx.finish().as_ref())
    }
}

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

#[cfg(test)]
mod test {
    use crate::merkle::*;

    fn test_paths_with_num(num: usize) {
        let mut merkle = MerkleTree::new();

        for i in 0..num {
            merkle.push_leaf(&[i as u8]);
        }

        let root = merkle.compute_root();

        for i in 0..num {
            println!("Testing {:?} {:?}", num, i);
            let paths: Vec<u8> = merkle.get_paths(i);
            let computed_root = root_from_paths(i, &[i as u8], &paths);

            assert_eq!(root, computed_root);
        }
    }

    #[test]
    fn power_of_two() {
        test_paths_with_num(2);
        test_paths_with_num(4);
        test_paths_with_num(8);
        test_paths_with_num(16);
    }

    #[test]
    fn not_power_of_two() {
        test_paths_with_num(1);
        test_paths_with_num(20);
    }
}
